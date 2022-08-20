from charm.toolbox.pairinggroup import PairingGroup, ZR, G1, G2, GT
from charm.toolbox.PKSig import PKSig

from functools import reduce

class ElGamal():
    def __init__(self, group):
        self.group = group
        self.e_1 = self.group.init(G1)
        self.e_2 = self.group.init(G2)
        self.e_t = self.group.init(GT)
        
        self.g = self.group.random(G1)

    def keygen(self):
        dk = self.group.random(ZR)
        P = self.g ** dk
        return P, dk
    
    def encrypt(self, pk, m):
        s = self.group.random(ZR)
        ct = [self.g ** s, self.g ** m * pk ** s]
        return ct

    def decrypt(self, dk, pk, ct):
        return ct[1] * (ct[0] ** -dk)

class GS():
    def __init__(self, group):
        self.group = group
        self.e_1 = self.group.init(G1)
        self.e_2 = self.group.init(G2)
        self.e_t = self.group.init(GT)

    def gen(self, only_u = False, only_v = False):
        if not only_v:
            u_11 = self.group.random(G1)
            u_12 = self.group.random(G1)
            u_21 = self.group.random(G1)
            u_22 = self.group.random(G1)
            u_1 = (u_11, u_12)
            u_2 = (u_21, u_22)

        if not only_u:
            v_11 = self.group.random(G2)
            v_12 = self.group.random(G2)
            v_21 = self.group.random(G2)
            v_22 = self.group.random(G2)
            v_1 = (v_11, v_12)
            v_2 = (v_21, v_22)
        if only_u:
            return {"u": (u_1, u_2)}
        elif only_v:
            return {"v": (v_1, v_2)}
        else:
            return {"u": (u_1, u_2), "v": (v_1, v_2)}
    
    def F(X, Y):
        assert len(X) == 2
        assert len(Y) == 2

        return [[self.group.pair_prod([X[i]], [Y[j]]) for j in range(2)] for i in range(2)]

    def iota1(self, x):
        return (self.e_1, x)
    
    def iota2(self, x):
        return (self.e_2, x)
    
    def iotat(self, x):
        return ((self.e_t, self.e_t), (self.e_t, x))

    def iotat_hat(self, crs, Z):
        uu = [crs["u"][1][0], crs["u"][1][1] * crs["u"][0][0]]
        return self.F(uu, self.iota2(Z))
    
    def iotat_tilde(self, crs, Z):
        vv = [crs["v"][1][0], crs["v"][1][1] * crs["v"][0][0]]
        return self.F(self.iota1(Z), vv)

    def com1(self, crs, x):
        r_1 = self.group.random(ZR)
        r_2 = self.group.random(ZR)

        x_ = self.iota1(x)
        c = [self.e_1, self.e_1]

        for i in range(2):
            c[i] = x_[i] * crs["u"][0][i] ** r_1 * crs["u"][1][i] ** r_2
        
        return (c[0], c[1]), (r_1, r_2)
    
    def com2(self, crs, x):
        s_1 = self.group.random(ZR)
        s_2 = self.group.random(ZR)

        x_ = self.iota2(x)
        c = [self.e_2, self.e_2]

        for i in range(2):
            c[i] = x_[i] * crs["v"][0][i] ** s_1 * crs["v"][1][i] ** s_2
        
        return (c[0], c[1]), (s_1, s_2)

    def com_scalar_1(self, crs, x):
        r = self.group.random(ZR)
        c = [crs["u"][0][0]** r * crs["u"][1][0]** x, (crs["u"][1][1] * crs["u"][0][0]) ** x * crs["u"][0][1]  ** r]  
        return c, r
    
    def com_scalar_2(self, crs, x):
        s = self.group.random(ZR)
        c = [crs["v"][0][0] ** s * crs["v"][1][0]** x, (crs["v"][1][1] * crs["v"][0][0]) ** x * crs["v"][0][1]  ** s]  
        return c, s

    def prove_pairing_linear_1(self, B, R):
    # Proof of statements e(x_1, b_1)e(x_2, b_2)...e(x_n, b_n) = t with
    # B = [b_1, ..., b_n] and R = [R_1, ..., R_2] are the randomnesses 
    # used in the commitments of [x_1, ..., x_n]
        assert len(B) == len(R)
        pi = [1, 1]
        for i in range(len(B)):
            pi[0] *= B[i] ** R[i][0]
            pi[1] *= B[i] ** R[i][1]
        return {"pi": pi} 
    
    def prove_pairing_linear_2(self, A, S):
    # Proof of statements e(a_1, y_1)e(a_2, y_2)...e(a_n, y_n) = t with
    # A = [a_1, ..., a_n] and S = [S_1, ..., S_2] are the randomnesses 
    # used in the commitments of [y_1, ..., y_n]
        assert len(A) == len(S)
        theta = [1, 1]
        for i in range(len(A)):
            theta[0] *= A[i] ** S[i][0]
            theta[1] *= A[i] ** S[i][1]
        return {"theta": theta} 

    def prove_pairing_quadratic(self, crs, X, Y, A, B, G, R, S):
        
        assert len(A) == len(S)
        assert len(B) == len(R)
        assert len(Y) == len(S)
        assert len(X) == len(R)
        assert len(G) == len(S)
        assert len(G[0]) == len(R)
        
        pi = [[self.e_2, self.e_2], [self.e_2, self.e_2]]
        theta = [[self.e_1, self.e_1], [self.e_1, self.e_1]]
        for i in range(2):
            for j in range(2):
                for k in range(len(B)):
                    pi[i][j] *= self.iota2(B[k])[j] ** R[k][i]

        for i in range(2):
            for j in range(2):
                for k in range(len(A)):
                    theta[i][j] *= self.iota1(A[k])[j] ** S[k][i]
    
        T = [[self.group.random(ZR) for i in range(2)] for j in range(2)]
        RGS = [[-T[j][i] for j in range(2)] for i in range(2)]
        
        for i in range(2):
            for j in range(2):
                for k in range(len(X)):
                    for l in range(len(Y)):
                        pi[i][j] *= self.iota2(Y[l])[j] ** (G[k][l] * R[k][i])
                        theta[i][j] *= self.iota1(X[k])[j] ** (G[k][l] * S[l][i])
                        
                        RGS[i][j] += R[k][i] * G[k][l] * S[l][j]
        
        for i in range(2):
            for j in range(2):
                for k in range(2):
                    pi[i][j] *= crs["v"][k][j] ** RGS[i][k]
                    theta[i][j] *= crs["u"][k][j] ** T[i][k]

        return {"theta": theta, "pi": pi}

    def prove_multiscalar_linear_Bx(self, B, r):
    # Proof of statements B_1^x_1 * B_2^x_2 * ... * B_n^x_n = T with B = [B_1, ...,
    # B_n] and r = [r_1, ..., r_n] are the randomnesses used in the commitments
    # of [x_1, ..., x_n]
        assert len(B) == len(r)
        pi = self.e_2
        for i in range(len(B)):
            pi *= B[i] ** r[i]
        return {"pi": pi} 
    
    def prove_multiscalar_linear_Xb(self, b, R):
    # Proof of statements X_1^b_1 * X_2^b_2 * ... * X_n^b_n = T with b = [b_1, ...,
    # b_n] and R = [R_1, ..., R_n] are the randomnesses used in the commitments
    # of [X_1, ..., X_n]
        assert len(b) == len(R)
        pi = [0, 0]
        for i in range(len(b)):
            pi[0] += b[i] * R[i][0]
            pi[1] += b[i] * R[i][1]
        return {"pi": pi} 
    
    def prove_multiscalar_linear_Ay(self, A, s):
    # Proof of statements A_1^y_1 * A_2^y_2 * ... * A_n^y_n = T with A = [A_1, ...,
    # A_n] and s = [s_1, ..., s_n] are the randomnesses used in the commitments
    # of [y_1, ..., y_n]
        assert len(A) == len(s)
        theta = self.e_1
        for i in range(len(A)):
            theta *= A[i] ** s[i]
        return {"theta": theta} 

    def prove_multiscalar_linear_Ya(self, a, S):
    # Proof of statements Y_1^a_1 * Y_2^a_2 * ... * Y_n^a_n = T with a = [a_1, ...,
    # a_n] and S = [S_1, ..., S_n] are the randomnesses used in the commitments
    # of [Y_1, ..., Y_n]
        assert len(a) == len(S)
        theta = [0, 0]
        for i in range(len(a)):
            theta[0] += a[i] * S[i][0]
            theta[1] += a[i] * S[i][1]
        return {"theta": theta} 
    
    def prove_multiscalar_1(self, crs, y, X, b, A, G, s, R):
        assert len(X) == len(R)
        assert len(y) == len(s)
        assert len(A) == len(y)
        assert len(X) == len(b)
        assert len(G) == len(X)
        assert len(G[0]) == len(y)

        pi = [[self.e_1, self.e_1], [self.e_1, self.e_1]]
        theta = [self.e_1, self.e_1]

        vv = [crs["v"][1][0], crs["v"][1][1] * crs["v"][0][0]]
        T = [self.group.random(ZR) for i in range(2)]

        GS = [0 for i in range(len(R))]
        GY = [0 for i in range(len(R))]
        for k in range(len(R)):
            for l in range(len(s)):
                GS[k] += G[k][l] * s[l]
                GY[k] += G[k][l] * y[l]

        vv_exp = [0, 0]
        v1_exp = [-T[i] for i in range(2)]
        for i in range(2):
            for k in range(len(R)):
                vv_exp[i] += R[k][i] * b[k]
                vv_exp[i] += R[k][i] * GY[k]
                v1_exp[i] += R[k][i] * GS[k]

        for i in range(2):
            for j in range(2):
                pi[i][j] = vv[j] ** vv_exp[i] 
                pi[i][j] *= crs["v"][0][j] ** (v1_exp[i])

        for i in range(2):
            for j in range(len(A)):
                theta[i] *= self.iota1(A[j])[i] ** s[j]  
            for j in range(len(X)):
                theta[i] *= self.iota1(X[j])[i] ** GS[j]
            for j in range(2):
                theta[i] *= crs["u"][j][i] ** T[j]


        return {"pi": pi, "theta": theta} 
    
    def prove_multiscalar_2(self, crs, x, Y, a, B, G, r, S):
        assert len(Y) == len(S)
        assert len(x) == len(r)
        assert len(B) == len(x)
        assert len(Y) == len(a)
        assert len(G) == len(Y)
        assert len(G[0]) == len(x)

        pi = [self.e_2, self.e_2]
        theta = [[self.e_2, self.e_2], [self.e_2, self.e_2]]

        uu = [crs["u"][1][0], crs["u"][1][1] * crs["u"][0][0]]
        T = [self.group.random(ZR) for i in range(2)]
        RGS = [[-T[0], -T[1]]]

        GS = [[0 for i in range(len(r))] for j in range(2)] 
        RG = [0 for i in range(len(Y))]
        for k in range(len(r)):
            for l in range(len(S)):
                for i in range(2):
                    GS[i][k] += G[k][l] * S[l][i]
                    RGS[i] += r[k] * G[k][l] * S[l][i]
                RG[l] += r[k] * G[k][l]

        for i in range(2):
            for j in range(len(r)):
                pi[i] *= self.iota2(B[j])[i] ** r[j]
            for j in range(len(Y)):
                pi[i] *= self.iota2(Y[j])[i] ** RG[j]
            for j in range(2):
                pi[i] *= crs["v"][j][i] ** (RGS[j] - T[j])

        uu_exp = [0, 0]
        for i in range(2):
            for j in range(len(S)):
                uu_exp[i] += S[j][i] * a[j]
                uu_exp[i] += GS[i][j] * x[j]
        
            theta[i] = uu[i] ** uu_exp[i] * crs["u"][0][i] ** T[i]

        return {"pi": pi, "theta": theta} 

    def prove_multiscalar_quadratic(self, crs, x, y, a, b, G, r, s):
        assert len(y) == len(s)
        assert len(x) == len(r)
        assert len(b) == len(x)
        assert len(y) == len(a)
        assert len(G) == len(y)
        assert len(G[0]) == len(x)
       
        T = self.group.random(ZR)

        uu_exp = 0
        vv_exp = 0
        v1_exp = -T
        
        for i in range(len(r)):
            vv_exp += r[i] * b[i]
            for j in range(len(s)):
                vv_exp += r[i] * G[i][j] * y[j]
                v1_exp += r[i] * G[i][j] * s[j]
        
        for i in range(len(s)):
            uu_exp += s[i] * a[i]
            for j in range(len(r)):
                uu_exp += s[i] * G[j][i] * x[j]

        uu = [crs["u"][1][0], crs["u"][1][1] * crs["u"][0][0]]
        vv = [crs["v"][1][0], crs["v"][1][1] * crs["v"][0][0]]
        pi = [vv[i] ** vv_exp * crs["v"][0][i] ** v1_exp for i in range(2)]
        theta = [uu[i] ** uu_exp * crs["u"][0][i] ** T for i in range(2)]

        return {"pi": pi, "theta": theta}

    def verify_pairing_linear_1(self, crs, B, C, proof, t):
        assert len(B) == len(C)

        for i in range(2):
            for j in range(2):
                lhs = self.group.pair_prod([C[k][i] for k in range(len(C))], [self.iota2(B[k])[j] for k in range(len(C))])
                rhs = self.iotat(t)[i][j]
                rhs *= self.group.pair_prod([crs["u"][0][i], crs["u"][1][i]], [self.iota2(proof["pi"][k])[j] for k in range(2)])
                if lhs != rhs:
                    return False
        return True
    
    def verify_pairing_linear_2(self, crs, A, D, proof, t):
        assert len(A) == len(D)

        for i in range(2):
            for j in range(2):
                lhs = self.group.pair_prod([self.iota1(A[k])[i] for k in range(len(A))], [D[k][j] for k in range(len(D))])
                rhs = self.iotat(t)[i][j]
                rhs *= self.group.pair_prod([self.iota1(proof["theta"][k])[i] for k in range(2)], [crs["v"][0][j], crs["v"][1][j]])
                if lhs != rhs:
                    return False
        return True

    def verify_pairing_quadratic(self, crs, C, D, A, B, G, proof, t):
        assert len(B) == len(C)
        assert len(A) == len(D)
        
        assert len(G[0]) == len(D)
        assert len(G) == len(C)

        for i in range(2):
            for j in range(2):
                lhs = self.e_t
               
                lhs *= self.group.pair_prod([self.iota1(A[k])[i] for k in range(len(A))], [D[k][j] for k in range(len(D))])
                lhs *= self.group.pair_prod([C[k][i] for k in range(len(C))] , [self.iota2(B[k])[j] for k in range(len(B))])
                GD = [self.e_2] * len(C)
                for k in range(len(D)):
                    for l in range(len(C)):
                        GD[k] *=  D[k][j] ** G[k][l]
                lhs *= self.group.pair_prod([C[k][i] for k in range(len(C))], GD)
                 
                rhs = self.iotat(t)[i][j]
                rhs *= self.group.pair_prod([crs["u"][k][i] for k in range(2)], [proof["pi"][k][j] for k in range(2)])
                rhs *= self.group.pair_prod([proof["theta"][k][i] for k in range(2)], [crs["v"][k][j] for k in range(2)])
                
                if lhs != rhs:
                    return False
        return True

class LHSP():
    def __init__(self, k, pp):
        self.k = k 
        self.g_hat = pp["g_hat"]     
        self.h_hat = pp["h_hat"]
        self.group = pp["group"]
    
    def keygen(self):

        chi_i = [self.group.random(ZR) for i in range(self.k)]
        gamma_i = [self.group.random(ZR) for i in range(self.k)]

        g_hat_i = [self.g_hat ** chi_i[i] * self.h_hat ** gamma_i[i] for i in range(self.k)]

        sk = {"chi_i": chi_i, "gamma_i": gamma_i}
        pk = {"g_hat_i": g_hat_i}
        return sk, pk

    def sign(self, pk, sk, m):
        assert len(m) == self.k

        Z = reduce(lambda a, b: a * b, [m[i]**sk["chi_i"][i] for i in range(self.k)])
        R = reduce(lambda a, b: a * b, [m[i]**sk["gamma_i"][i] for i in range(self.k)])
        return {"Z": Z, "R": R}

    def sign_derive(pk, omega_i, sig_i):
        assert len(omega_i) == len(sig_i)
        pass

    def verify(self, pk, m, sig):
        lhs = self.group.pair_prod([sig["Z"], sig["R"]], [self.g_hat, self.h_hat])
        rhs = self.group.pair_prod(m, pk["g_hat_i"])

        return lhs == rhs
