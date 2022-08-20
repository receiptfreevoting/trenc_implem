from charm.toolbox.pairinggroup import PairingGroup, ZR, G1, G2, GT
from charm.toolbox.PKSig import PKSig
from charm.toolbox.PKEnc import PKEnc

from tools import GS, LHSP
from functools import reduce

class TRENC(PKEnc):
    def __init__(self, group, lb):
        PKEnc.__init__(self)
        self.lb = lb
        self.group = group 
        self.e_1 = self.group.init(G1)
        self.e_2 = self.group.init(G2)
        self.e_t = self.group.init(GT)
    
    def keygen(self, bit_by_bit = True):
        g = self.group.random(G1)
        g_hat = self.group.random(G2)

        # Note: h, h_hat, gi's and all the following randomly generated group
        # elements should be generated from the hash function
        h = self.group.random(G1)
        h_hat = self.group.random(G2)
        if bit_by_bit:
            g_i = [self.group.random(G1) for i in range(self.lb)]

        S = self.group.random(G1)
        T = self.group.random(G1)
    
        alpha_i = [self.group.random(ZR) for i in range(self.lb)]
        beta_i = [self.group.random(ZR) for i in range(self.lb)]
        f_i = [g ** alpha_i[i] * h ** beta_i[i] for i in range(self.lb)]
        
        gs = GS(self.group)
        if bit_by_bit:
            crs_1 = gs.gen() 
        else:
            crs_1 = gs.gen(only_v = True)
        crs_2 = gs.gen(only_u = True) 


        sk = {"alpha_i": alpha_i, "beta_i": beta_i}
        pk = {"g": g, "g_hat": g_hat, "h": h, "h_hat": h_hat, "S": S, "T": T,
                "f_i": f_i, "crs_1": crs_1, "crs_2": crs_2}
        if bit_by_bit:
            pk["g_i"] = g_i
        return pk, sk
    
    def lgen(self, pk):
        lhsp = LHSP(3, {"group": self.group, "g_hat": pk["g_hat"], "h_hat": pk["h_hat"]})
        osk, opk = lhsp.keygen()
        return {"osk": osk, "opk": opk}

    def lenc(self, pk, lk, m, bit_by_bit):
        lhsp = LHSP(3, {"group": self.group, "g_hat": pk["g_hat"], "h_hat": pk["h_hat"]})
        gs = GS(self.group)

        g = pk["g"]
        h = pk["h"]
        g_hat = pk["g_hat"]
        h_hat = pk["h_hat"]
        f_i = pk["f_i"]
        S = pk["S"]
        T = pk["T"]
        crs_1 = pk["crs_1"]
        crs_2 = pk["crs_2"]

        # Note: F, G, H should be generated from the hash function with opk as
        # input
        F = self.group.random(G1)
        G = self.group.random(G1)
        H = self.group.random(G1)

        # Step 1
        theta = self.group.random(ZR)
        c_1 = g ** theta
        c_2 = h ** theta
        if bit_by_bit:
            g_i = pk["g_i"]
            d_i = [g_i[i] ** m[i] * f_i[i] ** theta for i in range(self.lb)] 
        else:
            d_i = [g ** m[i] * f_i[i] ** theta for i in range(self.lb)] 

    
        # Step 2
        opk, osk = lk["opk"], lk["osk"]
        sigma_1 = lhsp.sign(opk, osk, [g, reduce(lambda x, y: x*y, d_i), c_1])
        sigma_2 = lhsp.sign(opk, osk, [1, reduce(lambda x, y: x*y, f_i), g])
        sigma_3 = lhsp.sign(opk, osk, [1, F, G])

        # Step 3
        C_Z, R_Z = gs.com1(crs_2, sigma_1["Z"])
        C_R, R_R = gs.com1(crs_2, sigma_1["R"])
        pi_hat_sig = gs.prove_pairing_linear_1([g_hat, h_hat], [R_Z, R_R])

        # Step 4
        a_hat = 1
        b_hat = 1
        w_hat = g_hat
        C_hat_a, S_a = gs.com2(crs_1, a_hat) 
        C_hat_b, S_b = gs.com2(crs_1, b_hat)
        C_hat_w, S_w = gs.com2(crs_1, w_hat)

        pi_ss = gs.prove_pairing_linear_2([S, T, H], [S_a, S_b, S_w])

        # Step 5
        if bit_by_bit:
            C_M_i = [0] * self.lb
            C_hat_M_i = [0] * self.lb
            S_M_i = [0] * self.lb
            R_M_i = [0] * self.lb
            for i in range(self.lb):
                C_M_i[i], R_M_i[i] = gs.com1(crs_1, g ** m[i]) 
                C_hat_M_i[i], S_M_i[i] = gs.com2(crs_1, g_hat ** m[i])
        
        C_hat_theta, S_theta = gs.com2(crs_1, g_hat ** theta)
        pi_1 = gs.prove_pairing_linear_2([c_1, g ** -1], [S_w, S_theta])
        pi_2 = gs.prove_pairing_linear_2([c_2, h ** -1], [S_w, S_theta])
        
        if bit_by_bit:
            pi_d_i = [0] * self.lb 
            for i in range(self.lb):
                pi_d_i[i] = gs.prove_pairing_linear_2([d_i[i], g_i[i] ** -1, f_i[i] ** -1], [S_w, S_M_i[i], S_theta])
        
        # Step 6
        # Quadratic proof
        if bit_by_bit:
            pi_01_1 = [0] * self.lb
            pi_01_2 = [0] * self.lb
            for i in range(self.lb):
                pi_01_1[i] = gs.prove_pairing_quadratic(crs_1, [g ** m[i]], [g_hat ** m[i]], [g], [1], [[-1]], [R_M_i[i]], [S_M_i[i]])
                pi_01_2[i] = gs.prove_pairing_quadratic(crs_1, [g ** m[i]], [g_hat ** m[i]], [g], [g_hat], [[0]], [R_M_i[i]], [S_M_i[i]])
             
        # Step 7
        x_hat = g_hat
        C_hat_x, S_x = gs.com2(crs_1, x_hat)
        pi_r_1 = gs.prove_pairing_linear_2([g, g ** -1], [S_w, S_x])
        pi_r_2 = gs.prove_pairing_linear_2([g, h ** -1], [S_w, S_x])
        
        if bit_by_bit:
            pi_r_d_i = [0] * self.lb
            for i in range(self.lb):
                pi_r_d_i[i] = gs.prove_pairing_linear_2([g, d_i[i] ** -1], [S_w, S_x])
        
        ct = {"c": [c_1, c_2, d_i], "C_Z": C_Z, "C_R": C_R, "sigma_2": sigma_2,
                "sigma_3": sigma_3, "pi_hat_sig": pi_hat_sig, "opk": opk, "F":
                F, "G": G, "H": H, "C_hat_a": C_hat_a, "C_hat_b":
                C_hat_b,"C_hat_w": C_hat_w, "pi_ss": pi_ss, "C_hat_theta":
                C_hat_theta, "C_hat_x": C_hat_x, "pi_1": pi_1, "pi_2": pi_2,
                "pi_r": [pi_r_1, pi_r_2] }
        if bit_by_bit:
            ct["C_M_i"] = C_M_i
            ct["C_hat_M_i"] = C_hat_M_i
            ct["pi_01"] = [pi_01_1, pi_01_2]
            ct["pi_d_i"] = pi_d_i
            ct["pi_r"].append(pi_r_d_i)
        return ct

    def encrypt(self, pk, m, bit_by_bit = True):
        assert len(m) == self.lb
        
        lk = self.lgen(pk)
        ct = self.lenc(pk, lk, m, bit_by_bit)
        return ct
    
    def verify(self, pk, ct):
        # Note: one should check that the elements of the public key are correctly
        # derived from the hash of g and g_hat 
        gs = GS(self.group)
        
        g = pk["g"]
        h = pk["h"]
        g_hat = pk["g_hat"]
        h_hat = pk["h_hat"]
        g_i = pk["g_i"]
        f_i = pk["f_i"]
        S = pk["S"]
        T = pk["T"]
        crs_1 = pk["crs_1"]
        crs_2 = pk["crs_2"]
      
        c_1 = ct["c"][0]
        c_2 = ct["c"][1]
        d_i = ct["c"][2]

        opk = ct["opk"]
        sigma_2 = ct["sigma_2"]
        sigma_3 = ct["sigma_3"]
        F = ct["F"]
        G = ct["G"]
        H = ct["H"]

        C_R = ct["C_R"]
        C_Z = ct["C_Z"]
        C_hat_a = ct["C_hat_a"]
        C_hat_b = ct["C_hat_b"]
        C_hat_w = ct["C_hat_w"]
        C_hat_theta = ct["C_hat_theta"]
        C_M_i = ct["C_M_i"]
        C_hat_M_i = ct["C_hat_M_i"]
        C_hat_x = ct["C_hat_x"]


        lhsp = LHSP(3, {"group": self.group, "g_hat": g_hat, "h_hat": h_hat})
        if (not lhsp.verify(opk, [1, reduce(lambda x, y: x*y, f_i), g], sigma_2)
            or not lhsp.verify(opk, [1, F, G], sigma_3)):
            return False
         
        pi_hat_sig = ct["pi_hat_sig"]
        t_hat_sig = self.group.pair_prod([g, reduce(lambda x, y: x*y, d_i), c_1], opk["g_hat_i"])
        if not gs.verify_pairing_linear_1(crs_2, [g_hat, h_hat], [C_Z, C_R], pi_hat_sig, t_hat_sig):
            return False
        
        pi_ss = ct["pi_ss"]
        t_ss = self.group.pair_prod([H], [g_hat])
        if not gs.verify_pairing_linear_2(crs_1, [S, T, H], [C_hat_a, C_hat_b, C_hat_w], pi_ss, t_ss):
            return False
        pi_1 = ct["pi_1"]
        t_1 = self.e_t
        if not gs.verify_pairing_linear_2(crs_1, [c_1, g ** -1], [C_hat_w, C_hat_theta], pi_1, t_1):
            return False

        pi_2 = ct["pi_2"]
        t_2 = self.e_t
        if not gs.verify_pairing_linear_2(crs_1, [c_2, h ** -1], [C_hat_w, C_hat_theta], pi_2, t_2):
            return False

        for i in range(self.lb):
            t_d_i = self.e_t
            pi_d_i = ct["pi_d_i"][i]
            if not gs.verify_pairing_linear_2(crs_1, [d_i[i], g_i[i] ** -1, f_i[i] ** -1], [C_hat_w, C_hat_M_i[i], C_hat_theta], pi_d_i, t_d_i):
                return False

            pi_01_1 = ct["pi_01"][0][i]
            t_pi_01_1 = self.e_t
            if not gs.verify_pairing_quadratic(crs_1, [C_M_i[i]], [C_hat_M_i[i]], [g], [self.e_2], [[-1]], pi_01_1, t_pi_01_1):
                return False
            pi_01_2 = ct["pi_01"][1][i]
            t_pi_01_2 = self.e_t
            if not gs.verify_pairing_quadratic(crs_1, [C_M_i[i]], [C_hat_M_i[i]], [g], [g_hat], [[0]], pi_01_2, t_pi_01_2):
                return False
            
        return True

    def decrypt(self, pk, sk, ct):
        if not self.verify(pk, ct):
            return "bot" 
        else:
            m = [1] * self.lb
            for i in range(self.lb):
                if ct["c"][2][i] == ct["c"][0]**sk["alpha_i"][i] * ct["c"][1]**sk["beta_i"][i]:
                    m[i] = 0
            return m
