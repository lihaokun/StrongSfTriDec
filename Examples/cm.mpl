with(ListTools):

####################
f1 := 2*x^2-x*y+4:
f2 := x*y-2*y^2+4:
sub := [x=x1+I*x2, y=y1+I*y2]:
f1 := expand(subs( sub, f1)):
f2 := expand(subs( sub, f2)):
p1 := Re(f1) assuming real:
p2 := Im(f1) assuming real:
p3 := Re(f2) assuming real:
p4 := Im(f2) assuming real:

################
nld := proc(d, nb_vars)
local l, i, j, p, x, vars;
l := [];
vars := [];
for i from 1 to nb_vars do
    p := -1;
    for j from 1 to nb_vars do
        if i=j then
           p := p+x||j^d;
        else
           p := p+x||j;
        end if;
    end do;
    l := [op(l), p];
    vars := [op(vars), x||i];
end do;
return l, vars;
end proc:

################
nqleven := proc(nb_vars, even_d)
local x, vars, eqs, i;
vars := [ x||1 ];
eqs := [ x||1^even_d-2 ];
for i from 2 to nb_vars do
    vars := [ x||i, op(vars)];
    eqs := [op(eqs), x||i^even_d + x||i^(even_d/2)- x||(i-1)];
od;
return eqs, vars;
end proc:

################
simplenql := proc(nbvar, d)
local x, eqs, i, vars;
vars := [ x||1 ];
eqs := [ x||1^d-2 ];
for i from 2 to nbvar do
    vars := [ x||i, op(vars) ];
    eqs := [op(eqs), x||i^d - x||(i-1)];
end do;
return eqs, vars;
end proc:

####################
cm :=
[
    [   #(1) 4-body-homog ((1)-(47) are from changbo's folder BCLM-cm14)
        [-2*p^3+2*p^3*phi^3-4*phi^3*s*p^2+5*phi^3*s^3*p-phi^3*s^5,
         -2*s*p^3-2*phi^3*s^2+phi^3*s^4-3*phi^3*s^2*p+2*phi^3*p,
         -2*s^2+s^4-4*s^2*p+phi^2+1+4*p
        ],
        [phi,s,p]
    ],
    [
        #(2) 5-body-homog
        [-6*p^3+4*p^3*phi^3+15*phi^3*s^3*p-3*phi^3*s^5-12*phi^3*s*p^2-3*phi^3*s*p+phi^3*s^3,
        -9*phi^3*s^2*p-5*phi^3*s^2-6*s*p^3+3*phi^3*s^4+5*phi^3*p,
        -12*s^2*p-6*s^2+3*s^4+4*phi^2+3+12*p
        ],
        [phi,s,p]
    ],
    [
        #(3) Arnborg-Lazard
        [x^2*y*z + x*y^2*z + x*y*z^2 + x*y*z + x*y + x*z + y*z,
        x^2*y^2*z + x*y^2*z^2 + x^2*y*z + x*y*z + y*z + x + z,
        x^2*y^2*z^2 + x^2*y^2*z + x*y^2*z + x*y*z + x*z + z + 1
        ],
        [z,y,x]
    ],
    [
        #(4) Arnborg-Lazard-rev
        [x^2*y*z + x*y^2*z + x*y*z^2 + x*y*z + x*y + x*z + y*z,
        x^2*y^2*z + x*y^2*z^2 + x^2*y*z + x*y*z + y*z + x + z,
        x^2*y^2*z ^2 + x^2*y^2*z + x*y^2*z + x*y*z + x*z + z + 1
        ],
        [x,y,z]
    ],
    [
        #(5) Barry
        [-x^5+y^5-3*y-1,
         5*y^4-3,
         -20*x+y-z 
        ],
        [z,y,x]
    ],
    [
        #(6) Caprasse
        [y^2*z+2*x*y*t-2*x-z,
         -x^3*z+4*x*y^2*z+4*x^2*y*t+2*y^3*t+4*x^2-10*y^2+4*x*z-10*y*t+2,
         2*y*z*t+x*t^2-x-2*z,
         -x*z^3+4*y*z^2*t+4*x*z*t^2+2*y*t^3+4*x*z+4*z^2-10*y*t-10*t^2+2
        ],
        [t,z,y,x]
    ],
    [
        #(7) Caprasse-Li
        [y^2*z+2*x*y*t-2*x-z,
         -x^3*z+4*x*y^2*z+4*x^2*y*t+2*y^3*t+4*x^2-10*y^2+4*x*z-10*y*t+2,
         2*y*z*t+x*t^2-x-2*z,
         -x*z^3+4*y*z^2*t+4*x*z*t^2+2*y*t^3+4*x*z+4*z^2-10*y*t-10*t^2+2
        ],
        [x,y,z,t]
    ],
    [
        #(8) chemical-reaction
        [2 - 7*x1 + x1^2*x2 - 1/2*(x3 - x1), 
        6*x1 - x1^2*x2 - 5*(x4 - x2 ),
        2 - 7*x3 + x3^2*x4 - 1/2*(x1 - x3 ),
        6*x3 - x3^2*x4 + 1 + 1/2*(x2 - x4 )
        ],
        [x1,x2,x3,x4]
    ],
    [
        #(9) circles
        [product( (x-'i'), 'i'=1..10) +1/100,
         product ( (x-'i')^2+(y-'i')^2-2, 'i'=1..5)+1/1000
        ],
        [x,y]
    ],
    [
        #(10) cyclic-5
        [a + b + c + d + e,
         a*b + b*c + c*d + d*e + e*a,
         a*b*c + b*c*d + c*d*e + d*e*a + e*a*b,
         a*b*c*d + b*c*d*e + c*d*e*a + d*e*a*b  + e*a*b*c,
         a*b*c*d*e - 1
        ],
        [e,d,c,b,a]
    ],
    [
        #(11) Czapor-Geddes-Wang
        [b-2,
         c*c*q*q-2*d*c*q*q+d*d*q*q-2*c*c*q+2*d*p*c*q+2*b*p*c*q+2*d*c*q-2*d*d*p*q+2*b*p*q-2*p*q-2*b*d*d*q-2*b*q+2*q+c*c-2*d*p*c-2*b*d*c+b*b*d*d*p*p-2*b*d*d*p*p+d*d*p*p+2*b*b*p*p+2*p*p-2*b*b*d*d*p+4*b*d*d*p-4*b*b*p+4*b*p+b*b*d*d+2*b*b-4*b+2,
         -b*p*c*q-p*c*q+b*c*q-2*c*q+2*d*p*q+d*q+p*c+b*b*c-b*c+2*c+b*b*d*p*p+b*d*p*p-2*d*p*p-2*b*b*d*p+b*d*p-d*p+b*b*d-2*b*d,
         -2*p*q-2*q-b*b*p*p+2*p*p+2*b*b*p-b*b+2,
         3*c*c*q*q-3*d*d*q*q-4*q*q-6*c*c*q+6*b*d*p*c*q+6*b*d*c*q+6*d*d*p*q+3*c*c+6*b*d*p*c-6*b*d*c+3*b*b*d*d*p*p-3*d*d*p*p+b*b*p*p-6*b*b*d*d*p-2*b*b*p+4*p+3*b*b*d*d+b*b
        ],
        [b,d,p,c,q]
    ],
    [
        #(12) fabfaux
        [30752*x^3 + 46128*y*x^2 - 216256*x + 46128*x*y^2 + 141980 + 30752*y^3- 216256*y,
        30752*x^3 + 46128*z*x^2 - 216256*x + 46128*x*z^2 + 141980 + 30752*z^3+ 216256*z,
        46128*y^3 + 46128*x*y^2 + 46128*z*y^2 + 46128*y*x^2 - 432512*y +46128*x*z*y + 46128*z^2*y + 46128*x^3 - 432512*x + 425940 +46128*z*x^2 - 432512*z + 46128*x*z^2 + 46128*z^3
        ],
        [z,y,x]
    ],
    [
        #(13) geometric-constraints
        [1/100 - 4*s*(s - 1)*(s - b)*(s - c),
         1/5 - b*c, 
         2*s - 1 - b - c
        ],
        [s,b,c]
    ],
    [
        #(14) GonzalezGonzalez
        [x^3 + y*x^2 + x + z,
         x^2*y +3*x +2,
         x^2-y*x+z
        ],
        [z,y,x]
    ],
    [
        #(15) Katsura-4
        [2*x^2 + 2*y^2 + 2*z^2 + 2*t^2 + u^2 - u ,
        2*x*y + 2*y*z + 2*z*t + 2*t*u - t ,
        2*x*z + 2*y*t + t^2 + 2*z*u - z ,
        2*x*t + 2*z*t + 2*y*u - y ,
        2*x + 2*y + 2*z + 2*t + u - 1
        ],
        [u,t,z,y,x]
    ],
    [
        #(16) lhlp1
        [2*x^7+2-3*x^2-x^4,
         x^2+2*y^2-5,
         x*z-1
        ],
        [x,y,z]
    ],
    [
        #(17) lhlp2
        [y*(320+1600*y^4-240*y^5-471*y^6+36*y^7-48*y^2+36*y^8),
        -40*y^2+3*y^3+6*y^4+8*x,
        -8*y*z-8-40*y^4+3*y^5+6*y^6
        ],
        [x,y,z]
    ],
    [
        #(18) lhlp3
        [2450*x^6-1241*x^4+196*x^2-49,
         86*x^2+35*y*x^2-77*y-14,
         175*x^4+70*x^2*z-76*x^2-154*z+21
        ],
        [x,y,z]
    ],
    [
        #(19) lhlp4
        [x^4+y^4-1,
         x^5*y^2-4*x^3*y^3+x^2*y^5-1
        ],
        [x,y]
    ],
    [
        #(20) lhlp5
        [-7*x*y*z+6*y*z-14*x*z+9*z-3*x*y-12*y-x+1,
         2*x*y*z-y*z+14*z+15*x*y+14*y-15*x,
         -8*x*y*z+11*y*z-12*x*z-5*z+15*x*y+2*y+10*x-14
        ],
        [x,y,z]
    ],
    [
        #(21) lhlp6
        [p1,p2,p3,p4
        ],
        [y1,x1,y2,x2]
    ],
    [
        #(22) neural-network
        [1 - c*x - x*y^2 - x*z^2,
         1 - c*y - y*x^2 - y*z^2,
         1 - c*z - z*x^2 - z*y^2, 
         8*c^6 + 378*c^3 - 27
        ],
        [z,c,y,x]
    ],
    [
        #(23) nld-3-4
        [x^3 + y + z + t- 1,
         x + y^3 + z + t -1,
         x + y + z^3 + t-1,
         x + y + z + t^3 -1
        ],
        [t,z,y,x]
    ],
    [
        #(24) nld-3-5
        [x^3 + y + z + t + u- 1,
         x + y^3 + z + t + u-1,
         x + y + z^3 + t + u-1,
         x + y + z + t^3 + u-1,
         x + y + z + t + u^3 -1
        ],
        [u,t,z,y,x]
    ],
    [
        #(25) nld-4-5
        [x^4 + y + z + t + u- 1,
         x + y^4 + z + t + u-1,
         x + y + z^4 + t + u-1,
         x + y + z + t^4 + u-1,
         x + y + z + t + u^4 -1
        ],
        [x,y,z,t,u]
    ],
    [
        #(26) nld-7-3
        [x^7 + y + z - 1,
         x + y^7 + z - 1,
         x + y + z^7 - 1
        ],
        [z,y,x]
    ],
    [
        #(27) nld-8-3
        [x^8 + y + z - 1,
         x + y^8 + z - 1,
         x + y + z^8 - 1
        ],
        [z,y,x]
    ],
    [
        #(28) nld-9-3
        [x^9 + y + z - 1,
         x + y^9 + z - 1,
         x + y + z^9 - 1
        ],
        [z,y,x]
    ],
    [
        #(29) nld-10-3
        [x^10 + y + z - 1,
         x + y^10 + z - 1,
         x + y + z^10 - 1
        ],
        [z,y,x]
    ],
    [
        #(30) nql-5-4
        nqleven(5,4)
    ],
    [
        #(31) nql-10-2
        nqleven(10,2)
    ],
    [
        #(32) nql-10-4
        nqleven(10,4)
    ],
    [
        #(33) nql-15-2
        nqleven(15,2)
    ],
    [
        #(34) p3p-special
        [x^2 + y^2 - x*y - 1,
         y^2 + z^2 - y*z - a^2,
         z^2 + x^2 - z*x - b^2,
         a^2 - 1 + b - b^2,
         3*b^6 + 56*b^4 - 122*b^3 + 56*b^2 + 3
        ],
        [b,a,x,y,z]
    ],
    [
        #(35) PlateForme2d-easy
        [(x1+5)^2+ (y1-0)^2 - 1,
         (x2-5)^2+ (y2-0)^2 - 1,
         (x3)^2  + (y3-5)^2 - 1,
         (x1-x2)^2 + (y1-y2)^2 - 3,
         (x1-x3)^2 + (y1-y3)^2 - 3,
         (x2-x3)^2 + (y2-y3)^2 - 3
        ],
        [y3,x3,y2,x2,y1,x1]
    ],
    [
        #(36) r-5
        [a^2 + a,
         a*b + b + a*b^2 +a,
         b^2*c + c + b*c^3 + b,
         c^3*d + d + c*d^4 + c,
         d^4*e + e + d*e^5 + d
        ],
        [e,d,c,b,a]
    ],
    [
        #(37) r-6
        [a^2 + a,
         a*b + b + a*b^2 +a,
         b^2*c + c + b*c^3 + b,
         c^3*d + d + c*d^4 + c,
         d^4*e + e + d*e^5 + d,
         e^5*f + f + e*f^6 + e
        ],
        [f,e,d,c,b,a]
    ],
    [
        #(38) Reif
        [x4*x13+x5*x14+x6*(1-x13-x14),
         x4*x15+x5*x16-x6*(x15+x16) ,
         x7*x13+x8*x14+x9*(1-x13-x14) ,
         x7*x15+x8*x16-x9*(x15+x16)-1 ,
         x10*x13+x11*x14+x12*(1-x13-x14) ,
         x10*x15+x11*x16-x12*(x15+x16) ,
         x1*x13+x2*x14+x3*(1-x13-x14) ,
         x1*x15+x2*x16-x3*(x15+x16) ,
         x1*x4*x13+x2*x5*x14+x3*x6*(1-x13-x14)-1 ,
         x1*x4*x15+x2*x5*x16-x3*x6*(x15+x16) ,
         x1*x7*x13+x2*x8*x14+x3*x9*(1-x13-x14) ,
         x1*x7*x15+x2*x8*x16-x3*x9*(x15+x16) ,
         x1*x10*x13+x2*x11*x14+x3*x12*(1-x13-x14) ,
         x1*x10*x15+x2*x11*x16-x3*x12*(x15+x16)-1
        ],
        [x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16]
    ],
    [
        #(39) Rose
        [7*y^4 - 20*x^2,
         2160*x*x*z^4+1512*x*z^4+315*z^4-4000*x*x-2800*x-490,
         -10080000*x^4*z^3-28224000*x^3*z^3-15288000*x*x*z^3-1978032*x*z^3-180075*z^3-23520000*x^4*y*z*z-41395200*x^3*y*z*z-26726560*x*x*y*z*z-7727104*x*y*z*z-852355*y*z*z+40320000*x^6*y*y*z+28800000*x^5*y*y*z+21168000*x^3*y*y*z+4939200*x*x*y*y*z+347508*x*y*y*z+67200000*x^5*y^3+94080000*x^4*y^3+40924800*x^3*y^3+2634240*x*x*y^3-2300844*x*y^3-432180*y^3
        ],
        [x,y,z]
    ],
    [
        #(40) simple-nql-20-30
        simplenql(20, 30)
    ],
    [
        #(41) Takeuchi-Lu
        [2*x1*(2 - x1 - y1 ) + x2 - x1,
         2*x2*(2 - x2 - y2 ) + x1 - x2,
         2*y1*(5 - x1 - 2*y1 ) + y2 - y1,
         y2*(3 - 2*x2 - 4*y2 ) + y1 - y2
        ],
        [x1,x2,y1,y2]
    ],
    [
        #(42) Themos-net
        [10000*d - 323536,
         (x-48)^2+(y-89)^2+(28)^2-(48*a+89*b+28*c)^2-d^2,
         (x-77)^2+(y-3)^2+(37)^2-(77*a+3*b+37*c)^2-d^2,
         (x-49)^2+(y-23)^2+(57)^2-(49*a+23*b+57*c)^2-d^2,
         a*x+b*y,
         a^2+b^2+c^2-1
        ],
        [d,c,b,a,y,x]
    ],
    [
        #(43) Trinks-2
        [45*y+35*u-165*v-36 ,
         35*y+25*z+40*t-27*u ,
         25*y*u-165*v^2+15*x-18*z+30*t ,
         15*y*z+20*t*u-9*x ,
         -11*v^3+x*y+2*z*t ,
         -11*u*v+3*v^2+99*x ,
         10000*v^3+6600*v+2673
        ],
        [v,u,z,t,y,x]
    ],
    [
        #(44) Trinks-difficult
        [45*y+35*u-165*v-36 ,
         35*y+25*z+40*t-27*u ,
         25*y*u-165*v^2+15*x-18*z+30*t ,
         15*y*z+20*t*u-9*x ,
         -11*v^3+x*y+2*z*t ,
         -11*u*v+3*v^2+99*x
        ],
        [v,u,z,t,y,x]
    ],
    [
        #(45) Uteshev-Bikker
        [x^2+x*y+y^2-2*x*z-4*y*z+3*z^2-3*x*t+2*y*t+t^2-3*x-2*y+3*z-2*t-2 ,
        2*x^2-x*y+y^2-x*z-y*z-6*z^2-x*t+y*t-5*z*t-3*t^2-5*x+y+5*z+2*t+5 ,
        -3-3*x*y+2*x*z+x*t^2-5*x*z^2-5*z^2*t-3*x*t-2*z*t+x*y*z+x*y*t-x^2*z+x^2-y^2+2*z^2+11*z-2*t-x+y+x^3+y^3-3*z^3+2*t^3-3*t^2-5*y^2*z+7*y*z^2 ,
        -15+2*x*y+11*x*t^2+5*x*z^2-z*t-4*x*y*z+6*x*y*t-x^2*z+3*x^2+2*y^2-z^2+4*z-10*t-35*x-14*y-x^3+6*y^3+15*z^3+4*t^3+5*t^2+6*y^2*z+4*y*z^2-x*z*t+6*x^2*y-12*x*y^2-7*y^2*t+2*y*t 
        ],
        [t,z,y,x]
    ],
    [
        #(46) wilkinson20
        [mul( (x-i),i=0..20 )+1/100],
        [x]
    ],
    [
        #(47) wilkinsonxy
        [mul( (x-i),i=1..5 )+1/100,
	     mul( (y-x-i),i=1..5)
        ],
        [x,y]
    ],
    [
        #(48) trivial-5 ((48) is from changbo's folder RCtest-zerodim)
        [x^2 -1,
         y^2 - 1,
         (x-1)*(y-1)
        ],
        [y,x]
    ],
    [   
        #(49) nld-4-4
        nld(4, 4)
    ],
    [
        #(50) nld-5-4
        nld(5, 4)
    ],
    [
        #(51) nld-6-4
        nld(6, 4)
    ],
    [
        #(52) nld-5-3
        nld(5, 3)
    ]
]: