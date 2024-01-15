
R<x>:=PolynomialRing(Rationals());
K<a>:=NumberField(x^3-x^2-3*x+1);
assert Discriminant(K) eq 148;

for lab in ["27a1", "64a1"]
    do E:=EllipticCurve(lab);
    rk, bool:=Rank(E);
    assert rk eq 0 and bool eq true;
    EK:=ChangeRing(E,K);
    assert #TorsionSubgroup(E) eq #TorsionSubgroup(EK);
    rk, bool:=Rank(EK);
    assert rk eq 0 and bool eq true; //i.e. E(K)=E(Q)
end for;

//