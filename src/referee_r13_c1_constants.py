from decimal import Decimal as D, getcontext
from math import factorial
getcontext().prec = 120
ln2 = D(2).ln(); ln10 = D(10).ln()

C17 = (D(17)/D(16))**65 / D(factorial(65))
rho0 = D(1)/(D(8)*(D(2887)*ln10 - D(64).ln()))
h0 = D(1)+rho0+C17
C0 = h0**65/D(factorial(65))
A4 = D(32)/D(3)*(D(1)-D(6)**(-31))
print("C17  =", C17)
print("rho0 =", rho0)
print("h0-1 =", h0-1)
print("C0   =", C0)
print("A4   =", A4)
# published baseline: 32*log10(A4/C17)
print("published baseline log10 range = 32*log10(A4/C17) =", 32*(A4/C17).ln()/ln10)
print("new           log10 Mcrit      = 32*log10(A4/C0)  =", 32*(A4/C0).ln()/ln10)
# T2 corrected range 65/2 * log10(63/C0)
print("Theorem C exponent = 65/2*log10(63/C0) =", D(65)/2*(D(63)/C0).ln()/ln10)
print("old T2 target 65/2*log10(64/C17)      =", D(65)/2*(D(64)/C17).ln()/ln10)
print("65/2*log10(63/C17)                    =", D(65)/2*(D(63)/C17).ln()/ln10)
# consequence 8 n^3 <= 10^2942
print("8*10^(3*980) = 10^", (D(8)).log10()+2940, " <= 2942 ?", D(8)*D(10)**2940 <= D(10)**2942)
print("max n exponent: (2942 - log10 8)/3 =", (D(2942)-D(8).log10())/3)
print("published: (2887.45-log10 8)/3     =", (D('2887.45')-D(8).log10())/3)
# T3 family size
print("log10 m at M=2000 =", D(65)*D(2001)*D(2).log10())
# check case-1/case-2 crossing consistency: L<=m H^65/65! at H=h0 equals C0*m
print("C0/C17 =", C0/C17, " (17/16)^65 =", (D(17)/D(16))**65)
