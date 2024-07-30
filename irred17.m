//We first check the claims made about the elliptic curve with Cremona label 34a1

E:=EllipticCurve("34a1");

K<a>:=CompositeFields(QuadraticField(2), QuadraticField(3))[1];
assert a^4-10*a^2+1 eq 0;                       // a = sqrt(2)+sqrt(3)

L:=QuadraticField(2);

EK:=BaseChange(E, K);                           //Base change E over K
EL:=BaseChange(E,L);                            //Base change E over L

G:=Generators(EK);

assert #G eq 2;

assert G[1] in EL;
assert Order(G[1]) eq 6;

assert G[2] in EL;
assert Order(G[2]) eq 0;				//Therefore E(K)=E(L) where L=Q(sqrt2)

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
