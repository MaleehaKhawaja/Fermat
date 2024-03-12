Qx<x>:=PolynomialRing(Rationals());

E1:=HyperellipticCurve(4*x^3+1);
E1d:=EllipticCurve(E1);
E1d:=MinimalModel(E1d);
assert Discriminant(E1d) eq -27;

rk,tf:=Rank(E1d);
assert rk eq 0 and tf eq true;
MordellWeilGroup(E1d);

//

E:=EllipticCurve([0,2]);
E;
assert #TorsionSubgroup(E) eq 1;
rk, tf:=Rank(E);
assert rk eq 1 and tf eq true;
Generators(E);

//

C:=HyperellipticCurve(2*(-4*x^9+1));

J:=Jacobian(C);
BadPrimes(J);

J5:=BaseChange(J, GF(5));
#J5;
J13:=BaseChange(J, GF(13));
#J13;
assert Gcd(#J5, #J13) eq 1; 		//Reduction modulo 5 and modulo 13 shows there is no torsion on J.

TwoSelmerGroup(J); // rank bound is 1

cP:=J![x^3-1/2,1]; // infinite order so rank = 1

// Want to check that cP is not divisible by 3 in J(\Q).

p:=5;
q:=3;
Fp:=GF(p);
Fpz<z>:=PolynomialRing(Fp);
Cp:=HyperellipticCurve(2*(-4*z^9+1));
Jp:=Jacobian(Cp);
A,pi:=AbelianGroup(Jp);
Qp:=Jp![z^3-1/2,1]; // reduction of cP mod p
Qpi:=Qp@@pi;  // image of cP in the abelian group A
B,psi:=quo<A | q*A>;  // B=A/qA,  psi : A -> A/qA
assert  psi(Qpi) eq B!0 eq false; // Hence cP is not divisible by 3.

//

E:=HyperellipticCurve(6*(-4*x^3+1));
E,phi:=EllipticCurve(E);
E;
assert #TorsionSubgroup(E) eq 1;
rk, tf:=Rank(E);
assert rk eq 1 and tf eq true;
Generators(E);
phi;

C:=HyperellipticCurve(6*(-4*x^9+1));
J:=Jacobian(C);
BadPrimes(J);
J5:=BaseChange(J, GF(5));
#J5;
J13:=BaseChange(J, GF(13));
#J13;
assert Gcd(#J5, #J13) eq 1; 

TwoSelmerGroup(J); // rank bound is 1
cP:=J![x^3+1/2,3]; //infinite order so rank = 1

p:=11;
q:=3;
Fp:=GF(p);
Fpz<z>:=PolynomialRing(Fp);
Cp:=HyperellipticCurve(6*(-4*z^9+1));
Jp:=Jacobian(Cp);
A,pi:=AbelianGroup(Jp);
Qp:=Jp![z^3+1/2,3]; // reduction of cP mod p
Qpi:=Qp@@pi;  // image of cP in the abelian group A
B,psi:=quo<A | q*A>;  // B=A/qA,  psi : A -> A/qA
assert  psi(Qpi) eq B!0 eq false; // Hence cP is not divisible by 3.



