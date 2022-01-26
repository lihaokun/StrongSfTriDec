# h := discrim(a1*x^4 + x^5 + a2*x^3 + a3*x^2 + a4*x + a5, x):

# # (1)-(47) are from Wang Dongming - So1ving po1ynomia1 equations: Characteristic sets and triangu1ar systems
# # 共16个例子

wangzero :=
[
    [   #(2) wang_ex9
        [x^8 + 4*x^6*y^2 + 6*x^4*y^4 + 4*x^2*y^6 + y^8 - 2*x^6*y - 6*x^4*y^3 - 6*x^2*y^5 - 2*y^7 - 5*x^6 - 11*x^4*y^2 - 7*x^2*y^4 - y^6 + 10*x^4*y + 12*x^2*y^3 + 2*y^5 + 4*x^4 + 4*x^2*y^2 - 8*x^2*y,
        8*x^7 + 24*x^5*y^2 + 24*x^3*y^4 + 8*x*y^6 - 12*x^5*y - 24*x^3*y^3 - 12*x*y^5 - 30*x^5 - 44*x^3*y^2 - 14*x*y^4 + 40*x^3*y + 24*x*y^3 + 16*x^3 + 8*x*y^2 - 16*x*y,
        8*x^6*y + 24*x^4*y^3 + 24*x^2*y^5 + 8*y^7 - 2*x^6 - 18*x^4*y^2 - 30*x^2*y^4 - 14*y^6 - 22*x^4*y - 28*x^2*y^3 - 6*y^5 + 10*x^4 + 36*x^2*y^2 + 10*y^4 + 8*x^2*y - 8*x^2
        ],
        [x, y]
    ],
    [   #(7) wang_ex15
        [8*x^2-2*x*y-6*x*z+3*x+3*y^2-7*y*z+10*y+10*z^2-8*z-4,
         10*x^2-2*x*y+6*x*z-6*x+9*y^2-y*z-4*y-2*z^2+5*z-9,
         5*x^2+8*x*y+4*x*z+8*x+9*y^2-6*y*z+2*y-z^2-7*z+5
        ],
        [x, y, z]
    ],
    [
        #(8) wang_ex16
        [2 + 10*p^2 - 2*p*q - 2*q + c^2*(q - 1)^2 + 2*c*d*(1 - q)*(q - p) + 4*p*q*d*(d - c) + 4*d^2*(1 - 2*p) + 4*d^2*(p - q) + 4*d*c*(p - 1) + 4*p*q*(c + 1) - 8*p + d^2*(p - q)^2, 
        d*(2*p + 1)*(q - p) + c*(p + 2)*(1 - q) - 6*p*d + 2*c*(-p*q + p + q - 1) + 6*p^2*d, 
        -4*(p - 1)^2 + 2*p*(p - q) - 2*q + 2, 
        4 - 4*q^2 + 4*p + 3*c^2*(q - 1)^2 - 3*d^2*(p - q)^2 + 12*d^2*(p - 1)^2 + 4*p*(p - 2) + 12*d*c*(p + q + p*q - 1)
        ],
        [q, c, p, d]
    ],
    [
        #(10) wang_ex21
        [x + y + z + t + u,
         x*y + y*z + z*t + t*u + u*x,
         x*y*z + y*z*t + z*t*u + t*u*x + u*x*y,
         x*y*z*t + y*z*t*u + z*t*u*x + t*u*x*y + u*x*y*z,
         x*y*z*t*u + 1
        ],
        [x, y, z, t, u]
    ],
    [   #(13) wang_ex26
        [x^2 + y^2 + z^2,
         z*y*x,
         y^2*x^2 + z^2*x^2 + z^2*y^2,
         u^2 + 1/3*t^2,
         u^3 - t^2*u,
         2*x^2*u - y^2*u - z^2*u + y^2*t - z^2*t, 
         -y^2*x^2*u - z^2*x^2*u + 2*z^2*y^2*u - y^2*x^2*t + z^2*x^2*t,
         2*x^2*u^2 - y^2*u^2 - z^2*u^2 - 2*y^2*t*u + 2*z^2*t*u - 2/3*x^2*t^2 + 1/3*y^2*t^2 + 1/3*z^2*t^2,
         - y^2*x^2*u^2 - z^2*x^2*u^2 + 2*z^2*y^2*u^2 + 2*y^2*x^2*t*u - 2*z^2*x^2*t*u + 1/3*y^2*x^2*t^2 + 1/3*z^2*x^2*t^2 - 2/3*z^2*y^2*t^2,
         - 3*y^2*x^4*t*u^2 + 3*z^2*x^4*t*u^2 + 3*y^4*x^2*t*u^2 - 3*z^4*x^2*t*u^2 - 3*z^2*y^4*t*u^2 + 3*z^4*y^2*t*u^2
         + 1/3*y^2*x^4*t^3 - 1/3*z^2*x^4*t^3 - 1/3*y^4*x^2*t^3 + 1/3*z^4*x^2*t^3 + 1/3*z^2*y^4*t^3 - 1/3*z^4*y^2*t^3
        ],
        [x, y, z, t, u]
    ],
    [   #(14) wang_ex27
        [y + u + v - 1,
         z + t + 2*u - 3,
         y + t + 2*v - 1,
         x - y - z - t - u - v,
         t*u*x^2 - 1569/31250*y*z^3,
         z*v - 587/15625*y*t
        ],
        [x, y, z, t, u, v]
    ],
    [
        #(15) wang_ex28
        [x^2 - x + 2*y^2 + 2*z^2 + 2*t^2, 
         2*x*y + 2*y*z + 2*z*t - y, 
         2*x*z + y^2 + 2*y*t - z, 
         x + 2*y + 2*z + 2*t - 1
        ],
        [x, y, z, t]
    ],
    [   #(21) wang_ex34
        [B2*C2 + B3*C3 + B4*C4 + B5*C5 - 1/2,
         B2*C2^2 + B3*C3^2 + B4*C4^2 + B5*C5^2 - 1/3,
         B3*A32*C2 + B4*A42*C2 + B4*A43*C3 + B5*A52*C2 + B5*A53*C3 + B5*A54*C4 - 1/6,
         B2*C2^3 + B3*C3^3 + B4*C4^3 + B5*C5^3 - 1/4,
         B3*C3*A32*C2 + B4*C4*A42*C2 + B4*C4*A43*C3 + B5*C5*A52*C2 + B5*C5*A53*C3 + B5*C5*A54*C4 - 1/8,
         B3*A32*C2^2 + B4*A42*C2^2 + B4*A43*C3^2 + B5*A52*C2^2 + B5*A53*C3^2 + B5*A54*C4^2 - 1/12,
         B4*A43*A32*C2 + B5*A53*A32*C2 + B5*A54*A42*C2 + B5*A54*A43*C3-1/24,
         B2*C2^4 + B3*C3^4 + B4*C4^4 + B5*C5^4 - 1/5,
         B3*C3^2*A32*C2 + B4*C4^2*A42*C2 + B4*C4^2*A43*C3 + B5*C5^2*A52*C2 + B5*C5^2*A53*C3 + B5*C5^2*A54*C4 - 1/10,
         B3*C2^2*A32*C3 + B4*C2^2*A42*C4 + B4*C3^2*A43*C4 + B5*C2^2*A52*C2 + B5*C3^2*A53*C5 + B5*C4^2*A54*C5 - 1/15,
         B4*C4*A43*A32*C2 + B5*C5*A53*A32*C2 + B5*C5*A54*A42*C2
         + B5*C5*A54*A43*C3 - 1/30,
         B3*A32^2*C2^2 + B4*A42^2*C2^2 + 2*B4*A42*C2*A43*C3 + B4*A43^2*C3^2 + B5*A52^2*C2^2 + B5*A53^2*C3^2 + B5*A54^2*C4^2 + 2*B5*A52*C2*A53*C3 + 2*B5*A52*C2*A54*C4 + 2*B5*A53*C3*A54*C4 - 1/20,
         B3*A32*C2^3 + B4*A42*C2^3 + B4*A43*C3^3 + B5*A52*C2^3 + B5*A53*C3^3 + B5*A54*C4^3 - 1/20,
         B4*A43*C3*A32*C2 + B5*A53*C3*A32*C2 + B5*A54*C4*A42*C2 + B5*A54*C4*A43*C3- 1/40,
         B4*A43*A32*C2^2 + B5*A53*A32*C2^2 + B5*A54*A42*C2^2 + B5*A54*A43*C3^2- 1/60,
         B5*A54*A43*A32*C2-1/120
        ],
        [B2, B3, B4, B5, A32, A42, A43, A52, A53, A54, C4, C2, C3, C5]
    ],
    [   #(23) wang_ex36
        [U0^2 - U0 + 2*U1^2,
         U0 + 2*U1 - 1
        ],
        [U0, U1]
    ],
    [   #(24) wang_ex37
        [U0^2 - U0 + 2*U1^2 + 2*U2^2,
         2*U0*U1 + 2*U1*U2 - U1,
         U0 + 2*U1 + 2*U2 - 1
        ],
        [U0, U1, U2]
    ],
    [   #(25) wang_ex38
        [U0^2 - U0 + 2*U1^2 + 2*U2^2 + 2*U3^2,
         2*U0*U1 + 2*U1*U2 + 2*U2*U3 - U1,
         2*U0*U2 + U1^2 + 2*U1*U3 - U2,
         U0 + 2*U1 + 2*U2 + 2*U3 - 1
        ],
        [U0, U1, U2, U3]
    ],
    [   #(26) wang_ex39
        [
         U0^2 - U0 + 2*U1^2 + 2*U2^2 + 2*U3^2 + 2*U4^2,
         2*U0*U1 + 2*U1*U2 + 2*U2*U3 + 2*U3*U4 - U1,
         2*U0*U2 + U1^2 + 2*U1*U3 + 2*U2*U4 - U2,
         2*U0*U3 + 2*U1*U2 + 2*U1*U4 - U3,
         U0 + 2*U1 + 2*U2 + 2*U3 + 2*U4 - 1
        ],
        [U4, U3, U2, U1, U0]
    ],
    [   #(27) wang_ex40
        [U0^2 - U0 + 2*U1^2 + 2*U2^2 + 2*U3^2 + 2*U4^2 + 2*U5^2,
         2*U0*U1 + 2*U1*U2 + 2*U2*U3 + 2*U3*U4 + 2*U4*U5 - U1,
         2*U0*U2 + U1^2 + 2*U1*U3 + 2*U2*U4 + 2*U3*U5 - U2,
         2*U0*U3 + 2*U1*U2 + 2*U1*U4 + 2*U2*U5 - U3,
         2*U0*U4 + 2*U1*U3 + 2*U1*U5 + U2^2 - U4,
         U0 + 2*U1 + 2*U2 + 2*U3 + 2*U4 + 2*U5 - 1
        ],
        [U5, U4, U3, U2, U1, U0]
    ],
    [   #(28) wang_ex43
        [U4^4 - 20/7*A46^2,
         A46^2*U3^4 + 7/10*A46*U3^4 + 7/48*U3^4 - 50/27*A46^2 - 35/27*A46 - 49/216,
         A46^5*U4^3 + 7/5*A46^4*U4^3 + 609/1000*A46^3*U4^3 + 49/1250*A46^2*U4^3 - 27391/800000*A46*U4^3 - 1029/160000*U4^3 + 3/7*A46^5*U3*U4^2 + 3/5*A46^6*U3*U4^2 + 63/200*A46^3*U3*U4^2 + 147/2000*A46^2*U3*U4^2 + 4137/800000*A46*U3*U4^2 - 7/20*A46^4*U3^2*U4 - 77/125*A46^3*U3^2*U4 - 23863/60000*A46^2*U3^2*U4 - 1078/9375*A46*U3^2*U4 - 24353/1920000*U3^2*U4 - 3/20*A46^4*U3^3 - 21/100*A46^3*U3^3 - 91/800*A46^2*U3^3 - 5887/200000*A46*U3^3 - 343/128000*U3^3
        ],
        [U3, U4, A46]
    ],
    [   #(29) wang_ex45
        [45*P + 35*S - 165*B - 36,
         35*P + 40*Z + 25*T - 27*S,
         15*W + 25*P*S + 30*Z - 18*T - 165*B^2,
         -9*W + 15*P*T + 20*Z*S,
         W*P + 2*Z*T - 11*B^3,
         99*W - 11*S*B + 3*B^2
        ],
        [W, P, Z, T, S, B]
    ],
    [   #(30) wang_ex46
        [45*P + 35*S - 165*B - 36,
         35*P + 40*Z + 25*T - 27*S,
         15*W + 25*P*S + 30*Z - 18*T - 165*B^2,
         -9*W + 15*P*T + 20*Z*S,
         W*P + 2*Z*T - 11*B^3,
         99*W - 11*S*B + 3*B^2,
         B^2 + 33/50*B + 2673/10000
        ],
        [W, P, Z, T, S, B]
    ]
]: