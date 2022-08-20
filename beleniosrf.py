from charm.toolbox.pairinggroup import PairingGroup, ZR, G1, G2, GT
from charm.toolbox.PKSig import PKSig
from charm.toolbox.PKEnc import PKEnc

from tools import GS

from functools import reduce

class SRC():
    def __init__(self, k, pp):
        self.group = pp["group"]
        self.e_1 = self.group.init(G1)
        self.e_2 = self.group.init(G2)
        self.e_t = self.group.init(GT)

        self.k = k
        
        g_1 = self.group.random(G1)
        g_2 = self.group.random(G2)


        z = self.group.random(G1)
        u = [self.group.random(G1) for i in range(k+1)]

        self.pp = {"g": [g_1, g_2], "z": z, "u": u}
        self.gs = GS(self.group)
        self.elgamal = ElGamal(self.group)

    def F(self, m):
        assert len(m) == self.k
        
        f = self.pp["u"][0]
        for i in range(self.k):
            f *= self.pp["u"][i+1] ** m[i]
        return f

    def F_bin(self, m):
        assert len(m) == self.k
        
        f = self.pp["u"][0]
        for i in range(self.k):
            if m[i] == 1:
                f *= self.pp["u"][i+1]
        
        return f

    def H(self, h, x):
        return h[0] * h[1]# ** self.group.hash(x, ZR)

    def skeygen(self):
        x = self.group.random(ZR)
        X_1 = self.pp["g"][0] ** x
        X_2 = self.pp["g"][1] ** x
        
        Y = self.pp["z"] ** x
        vk = {"X": [X_1, X_2]}
        sk = {"Y": Y}
        return vk, sk

    def ekeygen(self):
        crs = self.gs.gen() 
        h_1 = self.group.random(G1)
        h_2 = self.group.random(G1)
        P, dk = self.elgamal.keygen()
        pk = {"crs": crs, "h": [h_1, h_2], "P": P}
        return pk, dk

    def encrypt(self, pk, vk, m):
        r = self.group.random(ZR)
        
        c_1 = self.pp["g"][0] ** r
        c_2 = self.F_bin(m) * pk["P"] ** r
        c_3 = self.H(pk["h"], vk) ** r

        C_m_i = [0] * self.k
        r_m_i = [0] * self.k
        C_hat_m_i = [0] * self.k
        s_m_i = [0] * self.k

        # Commitments
        for i in range(self.k):
            C_m_i[i], r_m_i[i] = self.gs.com_scalar_1(pk["crs"], m[i])
            C_hat_m_i, s_m_i[i] = self.gs.com_scalar_2(pk["crs"], m[i])

        w = vk["X"][0] ** r
        C_t, R_t = self.gs.com1(pk["crs"], w)
        C_hat_r, s_r = self.gs.com_scalar_2(pk["crs"], r)

        # proofs
        pi_r = self.gs.prove_multiscalar_linear_Ay([self.pp["g"][0]], [s_r])
        pi_t = self.gs.prove_multiscalar_1(pk["crs"], [r], [w], [-1], [vk["X"][0]], [[0]], [s_r], [R_t])
        pi_v = self.gs.prove_multiscalar_linear_Ay([self.H(pk["h"], vk)], [s_r])
        pi_m = self.gs.prove_multiscalar_linear_Ay([*self.pp["u"][1:], pk["P"]], [*s_m_i, s_r])
        pi_01 = [[0, 0] for i in range(self.k)]
        for i in range(self.k):
            # pi_i
            pi_01[i][0] = self.gs.prove_multiscalar_quadratic(pk["crs"], [m[i]], [m[i]], [1], [0], [[-1]], [r_m_i[i]], [s_m_i[i]])
            # C_m_i and C_hat_m_i have same m_i
            pi_01[i][1] = self.gs.prove_multiscalar_quadratic(pk["crs"], [m[i]], [m[i]], [1], [-1], [[0]], [r_m_i[i]], [s_m_i[i]])

        return {"c" : [c_1, c_2, c_3], "C_m_i": C_m_i, "C_hat_m_i": C_hat_m_i, "C_t": C_t, "C_hat_r": C_hat_r, "pi_r": pi_r, "pi_t": pi_t, "pi_v": pi_v, "pi_m": pi_m, "pi_01": pi_01}

    def sign(self, sk, m):
        assert len(m) == self.k
        s = self.group.random(ZR)
        sigma_1 = sk["Y"] * self.F(m) ** s 
        sigma_2 = self.g_1 ** s 
        sigma_3 = self.g_2 ** s 

        return [sigma_1, sigma_2, sigma_3]

    def sign_bin(self, pk, sk, m):
        assert len(m) == self.k
        s = self.group.random(ZR)
        sigma_1 = pk["Y"] * self.F_bin(m) ** s 
        sigma_2 = self.g_1 ** s 
        sigma_3 = self.g_2 ** s 
        return [sigma_1, sigma_2, sigma_3]


    def sign_plus(self, sk, pk, ct):
        assert len(ct) == 3
        s = self.group.random(ZR)

        sigma_1 = ct[0] ** s 
        sigma_2 = sk["Y"] * ct[1] ** s 
        sigma_3 = self.pp["g"][0] ** s 
        sigma_4 = self.pp["g"][1] ** s 
        sigma_5 = pk["P"] ** s
        return [sigma_1, sigma_2, sigma_3, sigma_4, sigma_5]

    def verif(self, vk, m, sig):
        return self.group.pair_prod([sig["sigma"][0] ** -1, self.z, self.F(m)], [self.g_2, vk["X"][1], sig["sigma"][2]]) == self.e_t and self.group.pair_prod([sig["sigma"][1], self.g_1 ** -1], [self.g_2, sig["sigma"][2]]) == self.e_t
    
    def verif_bin(self, vk, m, sig):
        return self.group.pair_prod([sig["sigma"][0] ** -1, self.z, self.F_bin(m)], [self.g_2, vk["X"][1], sig["sigma"][2]]) == self.e_t and self.group.pair_prod([sig["sigma"][1], self.g_1 ** -1], [self.g_2, sig["sigma"][2]]) == self.e_t

    def verify_plus(self, vk, pk, ct, sigma):
        #return {"c" : [c_1, c_2, c_3], "C_m_i": C_m_i, "C_hat_m_i": C_hat_m_i, "C_t": C_t, "C_hat_r": C_hat_r, "pi_r": pi_r, "pi_t": pi_t, "pi_v": pi_v, "pi_m"}
        pi_r = ct["pi_r"]
        t_r = ct["c"][0] 
        if not gs.verify_multiscalar_linear_(pk["crs"], [g_hat, h_hat], [C_Z, C_R], pi_hat_sig, t_r):
            return False

        return True


class BELENIOSRF(PKEnc):
    def __init__(self, group, lb):
        PKEnc.__init__(self)
        self.lb = lb
        self.group = group
        self.e_1 = self.group.init(G1)
        self.e_2 = self.group.init(G2)
        self.e_t = self.group.init(GT)
   
        self.SRC = SRC(k = lb, pp = {"group": self.group})

    def keygen(self, securityparam=1):
        return self.SRC.ekeygen()

    def encrypt(self, pk, m):
        assert len(m) == self.lb

        vk, sk = self.SRC.skeygen() 
        c = self.SRC.encrypt(pk, vk, m)
        sigma = self.SRC.sign_plus(sk, pk, c["c"])
        return {"c": c, "sigma": sigma, "vk": vk}
    
    def verify(self, pk, ct):
        return True 

    def decrypt(self, pk, sk, ct):
        if not self.verify(pk, ct):
            return "bot" 
        else:
            F = self.SRC.decrypt(dk, vk, ct)
            for i in range(2**20):
                if self.F(i) == F:
                    return i
            return "bot"
