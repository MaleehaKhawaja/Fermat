//The following code supports the 
//proof of Lemma 4.4

K<th>:=CompositeFields(QuadraticField(2),QuadraticField(3))[1];

OK:=MaximalOrder(K);

P:=Factorisation(2*OK)[1,1];

assert Valuation(2*OK,P) eq 4; // totally ramified

assert #RayClassGroup(P^2,[1,2,3,4]) eq 2;
assert #RayClassGroup(1*OK,[1,2,3,4]) eq 2;


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
