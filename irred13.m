//We first check the claims made about the elliptic curve with Cremona label 26b1.

E:=EllipticCurve("26b1");
K:=CompositeFields(QuadraticField(2),QuadraticField(3))[1];

EK:=ChangeRing(E,K);
assert #TorsionSubgroup(E) eq #TorsionSubgroup(EK);
for d in [2,3,6]
	do Rank(QuadraticTwist(E,d));					//Therefore E(K)=E(L) where L=Q(sqrt3)
end for;

//We compute the map between X0(26) and the elliptic curve with Cremona label 26b1.

X:=SimplifiedModel(SmallModularCurve(26));
X;
Aut:=Automorphisms(X);
w:=Aut[4];
G:=AutomorphismGroup(X, [w]);


E,phi:=CurveQuotient(G);
E;
//This is the minimal model of E

//We check that we have the right elliptic curve.
CremonaReference(E);

eqs:=DefiningEquations(phi);
KX<a,b>:=FunctionField(X);
eqsab:=[Evaluate(f,[a,b,1]): f in eqs];

A:=eqsab[1]/eqsab[3];
B:=eqsab[2]/eqsab[3];

//We check that (A,B) is indeed a point on E.

(B^2)+(A*B)+B-(A^3)+(A^2)+(3*A)-3;

A;

B;

//Let L=Q(sqrt3). We show there are no non-exceptional quadratic 
//points on the quadratic twist of X over L.

X:=SimplifiedModel(SmallModularCurve(26));
X3:=QuadraticTwist(X,3);
J3:=Jacobian(X3);
assert IsLocallySolvable(X3, 3) eq false; //X has no points over Q3, thus X(Q) is empty.

//Let L = Q(sqrt(3)). We show that there are no L-rational points on the curve C where C is the following hyperelliptic curve.

Qx<x>:=PolynomialRing(Rationals());
f:=-32*x^6 - 12*x^4 + 20*x^2 + 13;
C:=HyperellipticCurve(f);
L<a>:=NumberField(x^2-3);
CL:=ChangeRing(C,L);
OL:=IntegerRing(L);
Q:=Factorisation(13*OL)[1][1];

assert IsLocallySolvable(CL, Q) eq false; 
