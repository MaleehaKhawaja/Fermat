K<th>:=CompositeFields(QuadraticField(2),QuadraticField(3))[1];

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
