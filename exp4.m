//We check our claims about 
//the elliptic curves 32a1 and 64a1

E:=EllipticCurve("32a1");

L:=QuadraticField(2);

EL:=ChangeRing(E,L);
assert Rank(EL) eq 0;
assert #TorsionSubgroup(E) eq #TorsionSubgroup(EL);

assert #TorsionSubgroup(E) eq 4;
Points(E:Bound:=10);

//

E:=EllipticCurve("64a1");
L:=QuadraticField(2);

EL:=ChangeRing(E,L);
assert Rank(EL) eq 0;
assert #TorsionSubgroup(EL) eq 8;

Points(EL:Bound:=10);
