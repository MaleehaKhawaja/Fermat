//We check that the majority of the proof of Theorem 1.1 
//generalises to Q(sqrt2, sqrt11)

//The following code shows that the lowered 
//level is P or P^4 when p ge 17 or p = 13 and ord_P(b) ge 2

K<th>:=CompositeFields(QuadraticField(2),QuadraticField(11))[1];

OK:=MaximalOrder(K);

P:=Factorisation(2*OK)[1,1];

assert Valuation(2*OK,P) eq 4; // totally ramified


// Want the map Phi : OK^* --> R^* / (R^*)^2     R=OK/P^9


R,pi:=quo<OK | P^9>;

V,mu:=UnitGroup(R);  // mu : V --> R     V=R*

W,k:=quo<V | 2*V>;  // W = R^* / (R^*)^2

U,phi:=UnitGroup(OK);   // U = OK*

G:=OrderedGenerators(U);

Phi := hom< U ->  W |  [ k((pi(phi(g)))@@mu) : g in G ] >;

Q,l := quo< W | Image(Phi) >;

assert #Q eq 2;

lambdas := [ (mu((q@@l)@@k))@@pi  : q in Q];

assert lambdas[1] eq 1;

lam:=lambdas[2];

KT<T>:=PolynomialRing(K);
L:=ext<K | T^2-lam>;
D:=Discriminant(MaximalOrder(L));
assert Valuation(D,P) eq 2;

//
//The following code checks that the level is P^5
//when p=13 and ord_p(b)=1

K<th>:=CompositeFields(QuadraticField(2),QuadraticField(11))[1];

OK:=MaximalOrder(K);

P:=Factorisation(2*OK)[1,1];

assert Valuation(2*OK,P) eq 4; // totally ramified


// Want the map Phi : OK^* --> R^* / (R^*)^2     R=OK/P^9


R,pi:=quo<OK | P^6>;

V,mu:=UnitGroup(R);  // mu : V --> R     V=R*

W,k:=quo<V | 2*V>;  // W = R^* / (R^*)^2

U,phi:=UnitGroup(OK);   // U = OK*

G:=OrderedGenerators(U);

Phi := hom< U ->  W |  [ k((pi(phi(g)))@@mu) : g in G ] >;

Q,l := quo< W | Image(Phi) >;

assert #Q eq 1;

//

//The following code checks that the 
//proof of irreducibility generalises for p ge 19

K<th>:=CompositeFields(QuadraticField(2),QuadraticField(11))[1];

OK:=MaximalOrder(K);

P:=Factorisation(2*OK)[1,1];

assert Valuation(2*OK,P) eq 4; // totally ramified

assert #RayClassGroup(P^2,[1,2,3,4]) eq 2;
assert #RayClassGroup(1*OK,[1,2,3,4]) eq 2;

//

// isogeny signatures


auts:=Automorphisms(K);

sigs:=CartesianPower({0,2},4);

U,phi:=UnitGroup(OK);

units:=[phi(g) : g in OrderedGenerators(U)];

expunits:=[ K!phi(U.i) : i in [1..Ngens(U)] ]; //explicit units

twistednorm:=function(u,sig);
	return &*[ (u@auts[i])^sig[i] : i in [1..4]  ];
end function;

for sig in sigs do
	print sig;
	A:=&+[  (twistednorm(u,sig)-1)*OK   : u in units   ];
	if A eq 0*OK then
		print "failed";
	else 
		a:=Norm(A);
		print PrimeDivisors(a);
	end if;
	print "++++++++++++++++++++";
end for;

//


/*
Let K be a totally real field. 
Suppose there is a non-trivial solution to the Fermat eq over K with exponent p.
Want to compute the bound on p as given in Lemma 7.1 of [FS, FLT quad].
*/

/*
Let's assume we've already computed the lowered level
N_p=P. We should first determine the cuspidal Hilbert newforms over K
of weight (2,2) and level N_p=P.
*/

Aq := function(q);       //q should be a prime ideal not dividing Np.
    A := [];
    S := [Ceiling(2*SquareRoot(Norm(q)))..Floor(2*SquareRoot(Norm(q)))];
    for a in S
    do if a eq (Norm(q)+1) mod 4
        then Append(A, a);
        end if;
    end for;
    return A;
end function;

Bfq := function(f, q);
    Of := Integers(HeckeEigenvalueField(f));
    b1 := Norm(q)*((Norm(q)+1)^2-HeckeEigenvalue(Eigenform(f), q));
    b2 := 1;
    A := Aq(q);
    for a in A 
        do b2 := b2*(a-HeckeEigenvalue(Eigenform(f), q));
    end for;
    b := b1*b2;
    return b*Of;
end function;

Cf := function(f, n, K);
    Of := Integers(HeckeEigenvalueField(f));
    bf := 0*Of;
    primes := [q : q in PrimesUpTo(n, K) | IsOdd(Norm(q)) and IsPrime(Norm(q))];
    for q in primes
        do bf := bf + Bfq(f, q);
    end for;
    return Norm(bf);
end function;

//

Qx<x>:=PolynomialRing(Rationals());
K<th>:=CompositeFields(QuadraticField(2),QuadraticField(11))[1];
OK:=MaximalOrder(K);
P:=Factorisation(2*OK)[1,1];

assert Dimension(NewSubspace(HilbertCuspForms(K, P, 2))) eq 0;

//
M:=NewSubspace(HilbertCuspForms(K, P^4, 2));
decomp := NewformDecomposition(NewSubspace(M));

for f in decomp
    do Factorisation(Cf(f,90,K));
end for;

//

M:=NewSubspace(HilbertCuspForms(K, P^5, 2));
decomp := NewformDecomposition(NewSubspace(M));

for f in decomp
    do Cf(f,90,K);
end for;

//

//Irreducibility of mod 13 Galois representation

E:=EllipticCurve("26b1");
for d in [2,11,22]
    do Rank(QuadraticTwist(E,d));
end for;

//No torsion growth over quadratic or quartic fields by LMFDB
//Therefore E(K)=E(L) where L=Q(sqrt 22)

//Let L=Q(sqrt22). We show there are no non-exceptional quadratic 
//points on the quadratic twist of X over L.

X:=SimplifiedModel(SmallModularCurve(26));
X22:=QuadraticTwist(X,22);
J22:=Jacobian(X22);
assert IsLocallySolvable(X22, 11) eq false;

//

//Let L = Q(sqrt(22)). 
//We show that there are no L-rational points on the curve C where C is the following hyperelliptic curve.

Qx<x>:=PolynomialRing(Rationals());
f:=-32*x^6 - 12*x^4 + 20*x^2 + 13;
C:=HyperellipticCurve(f);
L<a>:=NumberField(x^2-22);
CL:=ChangeRing(C,L);
OL:=IntegerRing(L);
Q:=Factorisation(13*OL)[1][1];

assert IsLocallySolvable(CL, Q) eq false; 

//

//Irreducibility of mod 17 Galois representation

E:=EllipticCurve("34a1");
for d in [2,11,22]
    do Rank(QuadraticTwist(E,d));
end for;

//No torsion growth over relevant quadratic or quartic fields by LMFDB
//Therefore E(K)=E(L) where L=Q(sqrt 22)

//Let L=Q(sqrt2). We check that there are no L-rational points on the following plane curve C.

A<x,y>:=AffineSpace(Rationals(), 2);
f:=x^4-121*y^4+x^3+33*x*y^2-2*x^2+x+1;
C:=Curve(A, f);
C:=ProjectiveClosure(C);

L:=QuadraticField(2);
CL:=ChangeRing(C, L);

OL:=IntegerRing(L);
Q:=11*OL;

assert IsLocallySolvable(CL, Q) eq false; //i.e. There are no points on C defined over the completion of L at Q.