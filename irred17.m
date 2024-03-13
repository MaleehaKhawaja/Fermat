//We find the map between X0(34) and the elliptic curve with Cremona label 34a1 (which we denote here by E for ease).

Qx<x>:=PolynomialRing(Rationals());

Cdash:=HyperellipticCurve([x^4+x^3-2*x^2+x+1,-3*x]);

E, phi:=EllipticCurve(Cdash);

CremonaReference(E);

eqs:=DefiningEquations(phi);

KX<a,b>:=FunctionField(Cdash);

eqsab:=[Evaluate(f,[a,b,1]): f in eqs];

A:=eqsab[1]/eqsab[3];
B:=eqsab[2]/eqsab[3];

//We check that (A,B) is indeed a point on E.

assert (B^2) + (A*B) + (2*B) - (A^3) + (4*A) eq 0;

//Let L=Q(sqrt2). We check that there are no L-rational points on the following plane curve C.

A<x,y>:=AffineSpace(Rationals(), 2);
f:=x^4-9*y^4+x^3+9*x*y^2-2*x^2+x+1;
C:=Curve(A, f);
C:=ProjectiveClosure(C);

L:=QuadraticField(2);
CL:=ChangeRing(C, L);

OL:=IntegerRing(L);
Q:=3*OL;

assert IsLocallySolvable(CL, Q) eq false; //i.e. There are no points on C defined over the completion of L at Q.
