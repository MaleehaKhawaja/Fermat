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

X3:=QuadraticTwist(X,3);
J3:=Jacobian(X3);
assert TwoCoverDescent(X3) eq {}; //Therefore X3(Q) is empty by Bruin--Stoll.


//Let L = Q(sqrt(3)). We show that there are no L-rational points on the curve C where C is the following hyperelliptic curve.

Qx<x>:=PolynomialRing(Rationals());
C:=HyperellipticCurve(-2*x^6 - 3*x^4 + 20*x^2 + 52);

L<a>:=NumberField(x^2-3);

CL:=ChangeRing(C, L);

TwoCoverDescent(CL);
//This shows that the fake 2-selmer set of C/L is empty - thus, by Bruin-Stoll [5], C(L) is empty.
