Qx<x>:=PolynomialRing(Rationals());

L:=QuadraticField(3);

C:=HyperellipticCurve(2*(-4*x^9+1));

D:=HyperellipticCurve(2*(-4*x^3+1));

Genus(C);

J:=Jacobian(C);

// Reduction modulo 5 and modulo 13 shows there is no torsion on J.

TwoTorsionSubgroup(J);  // no 2-torsion

TwoSelmerGroup(J); // rank bound is 1

cP:=J![x^3-1/2,1]; // infinite order so rank = 1

// Want to check that cP is not divisible by 3 in J(\Q).

// Testing for saturation


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


S:=[]; // Set of primes where we know saturation.

for p in PrimesInInterval(5,300) do
	Fp:=GF(p);
	Fpz<z>:=PolynomialRing(Fp);
	Cp:=HyperellipticCurve(2*(-4*z^9+1));
	Jp:=Jacobian(Cp);
	A,pi:=AbelianGroup(Jp);
	Qp:=Jp![z^3-1/2,1];
	Qpi:=Qp@@pi;  // image of Q in the abelian group A
	prs:=PrimeDivisors(#A);
	for q in prs do
		B,psi:=quo<A | q*A>;  // B=A/qA,  psi : A -> A/qA
		if psi(Qpi) ne B!0 then
			Include(~S,q);
		end if;
	end for;
	Sort(~S);
	print p,S;
end for;

// Turns out S = [ 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 43, 47, 61, 73, 79, 139, 163, 199 ]

// This means that the index of <Q> in J(Q) is coprime to any element of S.

S = [ 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 43, 47, 61, 73, 79, 139, 163, 199 ];

goodp:=[];
M:=1;

for p in PrimesInInterval(5,300) do
	 Fp:=GF(p);
        Fpz<z>:=PolynomialRing(Fp);
        Cp:=HyperellipticCurve(2*(-4*z^9+1));
        Jp:=Jacobian(Cp);
	OJp:=Exponent(AbelianGroup(Jp));
	if Set(PrimeDivisors(OJp)) subset Set(S) then
		Append(~goodp,p);
		M:=LCM(M,OJp);
	end if;
	print p,goodp,M;
end for;

goodp:=[ 5, 7, 17, 23, 53, 59, 71, 73, 89, 107, 179, 197, 233, 251, 269, 293 ];

for p in goodp do
	Fp:=GF(p);
        Fpz<z>:=PolynomialRing(Fp);
        Cp:=HyperellipticCurve(2*(-4*z^9+1));
        Jp:=Jacobian(Cp);
        A,pi:=AbelianGroup(Jp);
        Qp:=Jp![z^3-1/2,1];
	Np:=Order(Qp);
	poss:=[0];
	nlist:=[1..(Np-1)];
	for n in nlist do
		nQp:=n*Qp;
		print n,nQp;
	end for;
end for;





