R<x> := PolynomialRing(Rationals());
//This codes supports the proof of Theorem 5.2


E := EllipticCurve("432b1");
K<a> := NumberField(x^4-10*x^2+1);
//We first check that E(K)=E(Q).
EK := ChangeRing(E, K);
for d in [2,3,6]
 do Rank(QuadraticTwist(E, d));
end for;
TorsionSubgroup(EK);



X := HyperellipticCurve(-4*x^6+1);
J := Jacobian(X);
RankBound(J);
PtsJ := Points(J : Bound := 1000);
P := PtsJ[4];
Order(P);
Chabauty(P);
//P has has infinite order thus we can use the Magma implementation of Chabauty to determine that C(Q)={(0, 1), (0, -1)}.



C3 := HyperellipticCurve(-4*x^6+27);
TwoCoverDescent(C3);
//This tells us that the fake 2-selmer set of C3/Q is empty. Thus, by Bruin-Stoll [5], C3(Q) is empty. 

C6 := HyperellipticCurve(-4*x^6+216);
TwoCoverDescent(C6);
//This tells us that the fake 2-selmer set of C3/Q is empty. Thus, by Bruin-Stoll [5], C3(Q) is empty. 

//----------------------------------------------------------------------------------------------------------------------------//

//We want to determine all Q-points on the curve C=C2. We will use Bruin's elliptic Chabauty method to do so.
f := -x^6 + 2;
C := HyperellipticCurve(f);
C;
Hk, AtoHk := TwoCoverDescent(C);
A<theta> := Domain(AtoHk);
deltas := {-1-theta, 1-theta};
{AtoHk(d): d in deltas} eq Hk;
L<a> := NumberField(x^3-2);
Lt<t> := PolynomialRing(L);

g := (t^4+a*t^2+a^2);
h := -(t^2-a);

//Checking that our factorisation of f is right
g*h eq Evaluate(f,t);

LTHETA<THETA> := quo<Lt|g>;
LTHETA;
j := hom<A->LTHETA|THETA>;
j;
eps := 1 + a + a^2;
//Checking that our choice of eps is the right one.
{Norm(j(delta)): delta in deltas} eq {eps};

E<X,Y,Z> := EllipticCurve([0,eps*a,0,(eps*a)^2,0]);
E;
//We want all the L-points on E such that X/eps is rational
P1 := ProjectiveSpace(Rationals(), 1);
EtoP1 := map<E->P1 | [X, eps*Z]>;

success, MWgrp, MWmap := PseudoMordellWeilGroup(E);
success;
MWgrp;

Factorization(Norm(Conductor(E)));
//E has good reduction away from 2 and 3

N, V, R, C := Chabauty(MWmap, EtoP1, 5);
N;
//N=4 -- Since R=1, this is the max. number of points on E such that X/eps is rational
V;
R;
//1
C;

//We determine the set of points on E such that X/eps is rational.
[ EtoP1( MWmap(P) ) : P in V ];
//This returns [ (1 : 0), (1 : 1), (0 : 1), (1 : 1) ]


