
//---------------------------------------------------------------//
//This part of the code supports the claims made in Lemma 13 of Khawaja's thesis 
//which is Lemma 3.1 in the arXiv version of the paper.

K<th>:=CompositeFields(QuadraticField(2),QuadraticField(3))[1];

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

//-----------------------------------------------------------//
//-----------------------------------------------------------//

// Get 2 levels: P, P^4

//We first show there are no newforms of level P.

H:=NewSubspace(HilbertCuspForms(K, P));
assert Dimension(H) eq 0;

//

H:=NewSubspace(HilbertCuspForms(K,P^4));
assert Dimension(H) eq 2;
eigs:=NewformDecomposition(H);

#eigs; // So looking for two non-isogenous elliptic curves
      // of conductor P^4

prs:=PrimesUpTo(50,K);   // all prime ideals of K of norm <=50
Exclude(~prs,P);

traces1:=[HeckeEigenvalue(Eigenform(eigs[1]),p) : p in prs];
traces2:=[HeckeEigenvalue(Eigenform(eigs[2]),p) : p in prs];

// SetVerbose("ECSearch",1);

//ells1:=EllipticCurveSearch(P^4,2 : Max:=1, Primes:=prs, Traces:=traces1);
//print ells1;

//ells2:=EllipticCurveSearch(P^4,1 : Max:=1, Primes:=prs, Traces:=traces2);
//print ells2;

E1:=EllipticCurve([
    th + 1,
    1/4*(-th^3 - th^2 - 3*th + 5),
    0,
    1/2*(-th^3 - 5*th),
    1/4*(th^3 + 7*th^2 - 9*th - 3)
]);

E2:=EllipticCurve([
    0,
    1/2*(-th^2 - 1),
    1/4*(th^3 + th^2 + 3*th + 3),
    th^2,
    1/4*(-3*th^3 - 17*th^2 - th + 1)
]);

assert Conductor(E1) eq P^4;
assert Conductor(E2) eq P^4;

assert [TraceOfFrobenius(E1,p) : p in prs] eq traces1;
assert [TraceOfFrobenius(E2,p) : p in prs] eq traces2;
assert traces1 ne traces2; // Therefore we have found two non-isogenous
			// elliptic curves of conductor P^4
tf1,D1:=HasComplexMultiplication(E1);
tf2,D2:=HasComplexMultiplication(E2);

assert tf1;
assert tf2;

assert D1 eq -24; // E_1 has complex multiplication by Z[sqrt{-24}]
assert D2 eq -3;  // E_2 has complex multiplication by Z[sqrt{-3}]

print jInvariant(E1);  // jInvariant is integral
print jInvariant(E2); // jInvariant is integral

assert jInvariant(E1) in OK;
assert jInvariant(E2) in OK;
