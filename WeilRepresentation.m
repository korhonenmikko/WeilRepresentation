
// generators of Sp(2l,r), for r odd prime

// C_t for 1 <= t <= l in Sp(2l,r)
// e_t -> -f_t
// f_t -> e_t
CmapSP := function(t,l,r)
 return 1+Matrix(GF(r), 2*l,2*l, [<t,2*l+1-t,1>, <2*l+1-t,t,-1>, <t,t,-1>, <2*l+1-t, 2*l+1-t,-1>]); 
end function;

// D_st (for 1 <= s < t <= l) in Sp(2l,r)
// f_t -> f_t + e_s
// f_s -> f_s + e_t
DmapSP := function(s,t,l,r)
 return 1+Matrix(GF(r), 2*l,2*l, [<s,2*l+1-t,1>, <t,2*l+1-s,1>]);
end function;

// E_t for 1 <= t <= l in Sp(2l,r)
// f_t -> f_t + e_t
EmapSP := function(t,l,r)
 return 1+Matrix(GF(r),2*l,2*l,[<t,2*l+1-t,1>]);
end function;

//
// For element g of SL(2,r) = Sp(2,r) (r prime)
// 
//     [a b]
// g = [c d]
//
// this function returns c1,c2,c3,c4 such that
// g = y^c1 * x^c2 * y^c3 * x^c4
//
// where x and y are standard transvections 
//
//     [1 1]           [1 0]
// x = [0 1]       y = [1 1]
//
sp2word := function(g)

	r := Characteristic(BaseRing(g));

	a := g[1][1];
    b := g[1][2];
    c := g[2][1];
    d := g[2][2];

    c1 := 0;
    c2 := 0;
    c3 := 0;
    c4 := 0;

    if c ne 0 then
     c1 := IntegerRing()!0;
     c2 := IntegerRing()!(a * (1-d)/c + b);
     c3 := IntegerRing()!c;
     c4 := IntegerRing()!((d-1)/c);
    end if;

    if c eq 0 then
     c1 := IntegerRing()!(-1);
     c2 := IntegerRing()!(1-d);
     c3 := IntegerRing()!a;
     c4 := IntegerRing()!((b+d-1)/a);
    end if;
	
	return c1,c2,c3,c4;
	
end function;

// <t,0,x> = E_t^x
// <0,t,x> = C_t^x
// <s,t,x> = D_{st}^x
CDEseqtoelt := function(L,l,r)
    g := Sp(2*l,r)!1;

    for x in L do
        // <0,t,x> = C_t^x
        if x[1] eq 0 then
            g := g*CmapSP(x[2], l, r)^x[3];
        // <t,0,x> = E_t^x
        elif x[2] eq 0 then
            g := g*EmapSP(x[1], l, r)^x[3];
        // <s,t,x> = D_st^x
        else
            g := g*DmapSP(x[1], x[2], l, r)^x[3];
        end if;
    end for;

    return g;
end function;

//
// given a nonzero vector v in GF(r)^(2l) as a list
// v = [a_1, ..., a_{2l}];
// find product of generators of Sp(2l,r) that maps v to e_1.
// (Transitivity of Sp(2l,r) on non-zero vectors.)
//
// representation:
// C_t; 1 <= t <= l      : <0,t>
// E_t; 1 <= t <= l      : <t,0>
// D_st; 1 <= s < t <= l : <s,t>
//
// F_t := C_t E_t^-1 C_t^-1
// Then F_t maps e_t -> e_t + f_t; fixes other basis vectors.
//
// e.g. for     [0  1]        [1 1]         [1 0]
//          C = [-1 0]    E = [0 1]     F = [1 1]
//
//  we have C*E^-1*C^-1 = F.
//
// Notation for tuples:
// <t,0,x> = E_t^x
// <0,t,x> = C_t^x
// <s,t,x> = D_{st}^x
//
// Thus for example:
// <0,1,1>, <t,0,-x>, <0,1,-1> = F_t^x
//
CDEsequenceSP :=  function(v)

    if {x : x in v} eq {0} then
		return [];
	end if;

    l := #v div 2;

    c := v[1];
	d := v[#v];
	
    if l eq 1 then
        r := Characteristic(Parent(c));
        g := Sp(2,r)!1;

        if c ne 0 then
            g := Matrix(GF(r), 2, 2, [c, 0, d, c^-1]);
        else
            g := Matrix(GF(r), 2, 2, [0, -d^-1, d, 0]);
        end if;

        c1,c2,c3,c4 := sp2word(g);
        L := [];

        // F^c1
        if c1 ne 0 then
         L := L cat [<0,1,1>, <1,0,-c1>, <0,1,-1>];
        end if;

        // E^c2
        if c2 ne 0 then
         L := L cat [<1,0,c2>];
        end if;

        // F^c3
        if c3 ne 0 then
         L := L cat [<0,1,1>, <1,0,-c3>, <0,1,-1>];
        end if;
        
        // E^c4
        if c4 ne 0 then
         L := L cat [<1,0,c4>];
        end if;

        // L gives s.t. ge_1 = v, so let's invert the list
        L := Reverse(L);
        for i in [1..#L] do
            x := L[i];
            L[i] := <x[1],x[2],-x[3]>;
        end for;

        // g = F^c1 * E^c2 * F^c3 * E^c4 ....
        return L;
    end if;

    //
    // write v = v' + v''.
    // where v' in <e_1, f_1>.
    // v'' in <e_2,f_2, ..., e_l, f_l>.
    //
	Lp := [v[j] : j in [2..(#v-1)]];

    // case where v'' = 0; get result from [c,d].
    if {x : x in Lp} eq {0} then
        return $$([c,d]);
    end if;

    K := $$(Lp);
    // adjust indices in K to fit desired l.
    for i in [1..#K] do
        x := K[i];
        if x[1] eq 0 then
            K[i] := <0,x[2]+1,x[3]>;
        elif x[2] eq 0 then
            K[i] := <x[1]+1,0,x[3]>;
        else
            K[i] := <x[1]+1,x[2]+1,x[3]>;
        end if;
    end for;

    // case where v' = 0.
    if (c eq 0) and (d eq 0) then

        // K maps v'' to e_2.
        // C_1 * D12^-1 * C_2 * C_1^-1 * D12 * C2^-1 maps e_2 to e_1.
        // 
        L := [<0,1,1>, <1,2,-1>, <0,2,1>, <0,1,-1>, <1,2,1>, <0,2,-1>];
        //     C_1     D_12^-1     C_2     C_1^-1     D_12    C_2^-1
        return L cat K;
    end if;

    // remaining case: both v' and v'' nonzero.
    // first conjugate v' to e_1, and v'' to e_2.
    // v = e_1 + e_2.
    // C_1 D_12^-1 C_1^-1 v = e_1.

    L := [<0,1,1>, <1,2,-1>, <0,1,-1>];
    //      C_1     D_12^-1   C_1^-1
    La := $$([c,d]);
    return L cat La cat K;

end function;

// for g in Sp(2l,r)
// return sequence such that for the corresponding element h;
// hge_1 = e_1 and hgf_1 = f_1.
// i.e. can use this to conjugate hyperbolic pairs (v,w) into (e_1,f_1).
CDEfirstpairSP := function(g)

	l := #Rows(g) div 2;
	r := Characteristic(BaseRing(g));

	if l eq 1 then
		c1,c2,c3,c4 := sp2word(g);
		L := [];

		// F^c1
		if c1 ne 0 then
			L := L cat [<0,1,1>, <1,0,-c1>, <0,1,-1>];
		end if;

		// E^c2
		if c2 ne 0 then
			L := L cat [<1,0,c2>];
		end if;

		// F^c3
		if c3 ne 0 then
			L := L cat [<0,1,1>, <1,0,-c3>, <0,1,-1>];
		end if;
			
		// E^c4
		if c4 ne 0 then
			L := L cat [<1,0,c4>];
		end if;

		// g = F^c1 * E^c2 * F^c3 * E^c4 ....
		// Invert the list to get desired result
		L := Reverse(L);
		for i in [1..#L] do
				x := L[i];
				L[i] := <x[1],x[2],-x[3]>;
		end for;
		
		return L;
	end if;

	// for the remainder, we have l > 1.

	v := Transpose(g)[1];
	v := [v[j] : j in [1..#Rows(g)]];

	L := CDEsequenceSP(v);
	h := CDEseqtoelt(L,l,r) * g;

	// he_1 = e_1
	// he_n = w = c e_1 + f_1 + v''
	// find additional such that (e_1,w) mapped to (e_1,f_1).

	c := h[1][2*l];

	// E_1^-c * (c e_1 + f_1) = f_1.
	if c ne 0 then
		L := [<1,0,IntegerRing()!(-c)>] cat L;
	end if;

	w := [h[j][2*l] : j in [2..(2*l-1)]];

	// if v'' = 0, we are done
	if {x : x in w} eq {0} then
		return L;
	end if;

	// this will map v'' to e_2.
	K := CDEsequenceSP(w);
	// adjust indices in K to fit desired l.
	for i in [1..#K] do
		x := K[i];
		if x[1] eq 0 then
			K[i] := <0,x[2]+1,x[3]>;
		elif x[2] eq 0 then
			K[i] := <x[1]+1,0,x[3]>;
		else
			K[i] := <x[1]+1,x[2]+1,x[3]>;
		end if;
	end for;

	// D_12^-1 maps (e_1,f_1+e_2) to (e_1, f_1).

	return [<1,2,-1>] cat K cat L;

end function;

//
// g = element of Sp(2l,r), where r is a prime.
// return sequence corresponding to g.
CDEwordSP := function(g)

	l := #Rows(g) div 2;
	r := Characteristic(BaseRing(g));

	if l eq 1 then
		c1,c2,c3,c4 := sp2word(g);
		L := [];

		// F^c1
		if c1 ne 0 then
			L := L cat [<0,1,1>, <1,0,-c1>, <0,1,-1>];
		end if;

		// E^c2
		if c2 ne 0 then
			L := L cat [<1,0,c2>];
		end if;

		// F^c3
		if c3 ne 0 then
			L := L cat [<0,1,1>, <1,0,-c3>, <0,1,-1>];
		end if;
			
		// E^c4
		if c4 ne 0 then
			L := L cat [<1,0,c4>];
		end if;
		
		return L;
	end if;

	L := CDEfirstpairSP(g);
	h := CDEseqtoelt(L,l,r) * g;

	gp := Submatrix(h,2,2,2*l-2,2*l-2);

	K := $$(gp);
	// adjust indices in K to fit desired l.
	for i in [1..#K] do
		x := K[i];
		if x[1] eq 0 then
			K[i] := <0,x[2]+1,x[3]>;
		elif x[2] eq 0 then
			K[i] := <x[1]+1,0,x[3]>;
		else
			K[i] := <x[1]+1,x[2]+1,x[3]>;
		end if;
	end for;

	// invert L
	L := Reverse(L);
	for i in [1..#L] do
				x := L[i];
				L[i] := <x[1],x[2],-x[3]>;
	end for;

	return L cat K;

end function;

//
// This function returns generators for the normalizer of an 
// absolutely irreducible extraspecial subgroup of GL(r^l, q).
//
// Here r is assumed to be an odd prime.
// The extraspecial group is the plus-type one, so of exponent r.
//
// r > 2 prime.
// l >= 1.
// q prime power such that r divides q-1.
//
// return f,At,Bt,Ct,Dst,Et
//
// f = generator for scalar matrices
// At = [A_1, ..., A_l]
// Bt = [B_1, ..., B_l]
// Ct = [C_1, ..., C_l]
//
// Dst = [D_{1,2}, D_{1,3}, ..., D_{1,l}, ..., D_{l-1,l}]
// Et  = [E_1, ..., E_l]
//
// The generators are chosen such that <Ct, Dst, Et> = Sp(2l,r)
// so Ct, Dst, Et provide generators for the Weil representation of Sp(2l,r).
//
ExtraSpecialNormalizerGenerators := function(r,l,q)

	K := GF(q);
	z := PrimitiveElement(K);

	// need to require that r divides q - 1
	// extraspecial group of order r^(1+2l)
	th := z^((q - 1) div r);

	f := ScalarMatrix(r^l, z);
	At := [];
	Bt := [];
	Ct := [];
	Dst := [];
	Et := [];

	A := DiagonalMatrix(K, [th^i : i in [0..(r-1)]]);
	B := Matrix(K, r, r, [<i+1,i,1> : i in [1..(r-1)]] cat [<1,r,1>]);
	C := Matrix(K, r, r, [<i,j,th^((i-1)*(j-1))> : i,j in [1..r]]);
	E := DiagonalMatrix(K, [th^((i*(i+r)) div 2) : i in [0..(r-1)]]);      
	I := IdentityMatrix(K, r);

	// scalar multiplier s.t. det(c*C) = 1:
	// c := (-r)^((r-1) div 2) * det(C)^-1;
	// c := (-r)^((r-1) div 2) * (&*[th^i - th^j : i,j in [0..(r-1)] | i gt j])^-1;
	c := (-1)^((r-1) div 2) * (&+[th^((i*(i+r)) div 2) : i in [0..(r-1)]])^-1;

	//
	// as a basis for r^l-dimensional vector space, we have tensor products
	// v_{x_1, ..., x_l} = v_{x_1} x ... x v_{x_l}, where 0 <= x_1, ..., x_l < r
	// here v_0, v_1, ..., v_{r-1} basis for the vector space of A,B,C,E.
	// 
	// At = [A_1, ..., A_l]
	// with A_i = I x ... x I x A x I ... x I (tensor product); 
	// where A is the i-th factor.
	// similarly for B_t,C_t,E_t using B,C,E.
	// A_t multiplies v_{x_1, ..., x_l} with th^(x_t)
	// B_t maps v_{x_1, ..., x_l} to v_{x_1,...,x_{t-1}, x_t + 1, x_{t+1}, ..., x_l}
	// C_t maps (...)
	// E_t multiplies v_{x_1, ..., x_l} with th^(x_t*(x_t+r)/2)
	//
	for i in [1..l] do
		if i eq 1 then
			tempA := A;
			tempB := B;
			tempC := C;
			tempE := E;
		else
			tempA := I;
			tempB := I;
			tempC := I;
			tempE := I;
		end if;

		for j in [2..l] do
			if j eq i then
				tempAX := A;
				tempBX := B;
				tempCX := C;
				tempEX := E;
			else
				tempAX := I;
				tempBX := I;
				tempCX := I;
				tempEX := I;
			end if;

			tempA := TensorProduct(tempA, tempAX);
			tempB := TensorProduct(tempB, tempBX);
			tempC := TensorProduct(tempC, tempCX);
			tempE := TensorProduct(tempE, tempEX);
		end for;

		At[i] := tempA;
		Bt[i] := tempB;
		Ct[i] := c*tempC; // multiply with scalar to get determinant 1
		Et[i] := tempE;
	end for;

	// construct D_{st} 1 <= s < t <= l
	// D_{st} multiplies v_{x_1, ..., x_l} with th^(x_s x_t).
	//
	// ordering of basis vectors in the tensor product:
	// w_0, w_1, ..., w_{r^l-1}
	// w_j = v_{x_1,...,x_l} with 0 <= j < r^l
	// then
	// j = x_l + x_{l-1} * r + ... + x_1 * r^(l-1)
	// so with base r expansion, we get the index j of v_{x_1, ..., x_l}
	// conversely for w_j, with base r expansion of j we get the values of x_1, ..., x_l
	
	Dst := []; 
	for s in [1..l] do
		for t in [s+1..l] do
			tempD := IdentityMatrix(K, r^l);

			for i in [1..r^l] do
				// sequence [i_1, ..., i_{l}]
				iseq := IntegerToSequence(i-1,r);
				iseq := iseq cat [0 : j in [1..(l-#iseq)]];
				ixt := iseq[l-t+1];
				ixs := iseq[l-s+1];
				tempD[i][i] := th^(ixt*ixs);
			end for;

			Append(~Dst, tempD);
		end for;
	end for;

	return f,At,Bt,Ct,Dst,Et;

end function;

//
// mu even:
// return generators for Sp(mu,q^v) as a subgroup of Sp(mu*v,q).
//
SymplecticFieldExtension := function(mu,v,q)
	// n = mu * v
	// for the rest of the function, we have mu > 1.
	n := mu*v;
	K := GF(q^v);
	z := PrimitiveElement(K);
    w := Generator(K, GF(q));
	R := PolynomialRing(GF(q));
	
    // We define f0 and phi0 with respect to basis 1,w,...,w^(v-1) of K/GF(q).

    // this is the minimal polynomial of w = Generator(K, GF(q)) over GF(q).
    pol := DefiningPolynomial(K, GF(q));
	w0 := Transpose(CompanionMatrix(pol));

  	f0 := ZeroMatrix(GF(q), v,v);
	for i in [1..v] do
        temp := Eltseq(z*w^(i-1), GF(q));
        temp := temp cat [0 : i in [1..(v-#temp)]];
        for j in [1..v] do
            f0[j][i] := temp[j];
        end for;
	end for;  

	f := DiagonalJoin([f0 : i in [1..mu]]);
	// X = matrix from GL(mu,K)
	// return matrix in GL(mu*v, K) as a block matrix, with v x v blocks.
	// X[i][j] = 0   => zero matrix as (i,j) block.
	// X[i][j] = z^k => f0^k as (i,j) block.
	
	f_extension := function(X)
		O := ZeroMatrix(GF(q), v);
		f_BLOCKS := [];
		for i in [1..mu] do
			for j in [1..mu] do
				if X[i][j] eq 0 then
					Append(~f_BLOCKS, O);
				else 
					s := Eltseq(X[i][j], GF(q));
                    temp_pol := elt< R | s>;
					Append(~f_BLOCKS, Evaluate(temp_pol,w0));
				end if;
			end for;
		end for;
		return BlockMatrix(mu,mu,f_BLOCKS);
	end function;

	G := Sp(mu,q^v);
	L := [f_extension(G.i) : i in [1..Ngens(G)]];

	o := ZeroMatrix(GF(q), mu*v);
	for i in [1..(mu div 2)] do
		for j1,j2 in [0..(v-1)] do
			temp := Trace(w^(j1+j2), GF(q));
			o[(i-1)*v + j1 + 1][(mu-i)*v + j2 + 1] := temp;
			o[(mu-i)*v + j2 + 1][(i-1)*v + j1 + 1] := -temp;
		end for;
	end for;
	
	M := TransformForm(o, "symplectic");
	L := [M*x*M^-1 : x in L];
	return L;
end function;

intrinsic WeilRepresentation( l::RngIntElt, r::RngIntElt, q::RngIntElt ) -> HomGrp
{ 
Returns the Weil Representation of Sp(2l,r) over GF(q) as a homomorphism Sp(2l,r) -> GL(r^l, q).
Here r is an odd prime power, such that the prime factor of r divides q-1.
}
require l ge 1 : "Argument 1 must be a positive integer";
require (#PrimeFactors(r) eq 1) and (r gt 1) and (r mod 2 eq 1) : "Argument 2 must be an odd prime power";
require (#PrimeFactors(q) eq 1) and (q gt 1) : "Argument 3 must be a prime power";

rf := Factorization(r)[1];
r0 := rf[1];
v := rf[2];

require (q mod r0) eq 1 : "Prime divisor of r must divide q-1";

    // If r is not a prime, we use the fact that 
    // the Weil representation of Sp(2l,r^v) arises 
    // as the restriction from Sp(2*l*v, r).
    if v gt 1 then
        // Weil representation of Sp(2*l*v, r0)
        m := $$(v*l, r0, q);
        Q := SymplecticFieldExtension(2*l,v,r0);
        return hom<Sp(2*l,r) -> GL(r^l,q) | [m(x) : x in Q]>;
    end if;

	f,A,B,C,D,E := ExtraSpecialNormalizerGenerators(r,l,q);
	G := Sp(2*l,r);
	V := [];

	for i in [1..Ngens(G)] do

		T := CDEwordSP(G.i);
		// Notation for tuples:
		// <t,0,x> = E_t^x
		// <0,t,x> = C_t^x
		// <s,t,x> = D_{st}^x
		// Thus:
		// <0,1,1>, <t,0,-x>, <0,1,-1> = F_t^x
		//
		temp := IdentityMatrix(GF(q),r^l);

		for j in [1..#T] do
			tu := T[j];
			if tu[1] eq 0 then
				// C_t^x
				temp := temp * C[tu[2]]^tu[3];
			elif tu[2] eq 0 then
				// E_t^x
				temp := temp * E[tu[1]]^tu[3];
			elif (tu[1] ne 0) and (tu[2] ne 0) then
				// D_{s,t}^x
				dindex := Binomial(l,2) - Binomial(l-tu[1]+1,2) + tu[2]-tu[1];
				temp := temp * D[dindex]^tu[3];
			end if;
		end for;

		V[i] := temp;
	end for;

	return hom<Sp(2*l,r) -> GL(r^l, q) | V>;

end intrinsic;


intrinsic IrreducibleWeilRepresentation(l::RngIntElt, r::RngIntElt, q::RngIntElt) -> HomGrp, HomGrp, HomGrp
{ 
Assume that r is an odd prime power, such that the prime factor of r divides q-1.
If q is odd, this function returns three representations f1,f2,f3 of Sp(2l,r), as homomorphisms:
    f1: Sp(2l,r) -> GL(r^l, q)
    f2: Sp(2l,r) -> GL((r^l+1)/2, q)
    f3: Sp(2l,r) -> GL((r^l-1)/2, q)
Here f1 is the Weil representation, which has f2 as a submodule and f3 as a quotient.
If q is odd, then f2,f3 are the irreducible composition factors of f1.
If q is even, then only f3 is irreducible.
}
require l ge 1 : "Argument 1 must be a positive integer";
require (#PrimeFactors(r) eq 1) and (r gt 1) and (r mod 2 eq 1) : "Argument 2 must be an odd prime power";
require (#PrimeFactors(q) eq 1) and (q gt 1) : "Argument 3 must be a prime power";

rf := Factorization(r)[1];
r0 := rf[1];
v := rf[2];

require (q mod r0) eq 1 : "Prime divisor of r must divide q-1";

    // If r is not a prime, we use the fact that 
    // the Weil representation of Sp(2l,r^v) arises 
    // as the restriction from Sp(2*l*v, r).
    if v gt 1 then
        // Relevant representation of Sp(2*l*v, r0)
        m1,m2,m3 := $$(v*l, r0, q);
        Q := SymplecticFieldExtension(2*l,v,r0);
        f1 := hom<Sp(2*l,r) -> GL(r^l,q) | [m1(x) : x in Q]>;
        f2 := hom<Sp(2*l,r) -> GL((r^l+1) div 2,q) | [m2(x) : x in Q]>;
        f3 := hom<Sp(2*l,r) -> GL((r^l-1) div 2,q) | [m3(x) : x in Q]>;
        return f1,f2,f3;
    end if;


	f,A,B,C,D,E := ExtraSpecialNormalizerGenerators(r,l,q);
	G := Sp(2*l,r);
	V := [];

	for i in [1..Ngens(G)] do
		T := CDEwordSP(G.i);
		// Notation for tuples:
		// <t,0,x> = E_t^x
		// <0,t,x> = C_t^x
		// <s,t,x> = D_{st}^x
		// Thus:
		// <0,1,1>, <t,0,-x>, <0,1,-1> = F_t^x
		//
		temp := IdentityMatrix(GF(q),r^l);

		for j in [1..#T] do
			tu := T[j];
			if tu[1] eq 0 then
				// C_t^x
				temp := temp * C[tu[2]]^tu[3];
			elif tu[2] eq 0 then
				// E_t^x
				temp := temp * E[tu[1]]^tu[3];
			elif (tu[1] ne 0) and (tu[2] ne 0) then
				// D_{s,t}^x
				dindex := Binomial(l,2) - Binomial(l-tu[1]+1,2) + tu[2]-tu[1];
				temp := temp * D[dindex]^tu[3];
			end if;
		end for;

		V[i] := temp;

	end for;

	// calculate conjugating matrix

	F := [];
	TUP := [];
	// n = 0 corresponds to v_{0,0,...,0}
	for n in [1..(r^l-1)] do
		if n in F then
			continue;
		end if;
		v := IntegerToSequence(n,r);
		v := v cat [0 : i in [1..(l-#v)]];
		w := [(-v[i]) mod r : i in [1..#v]];
		b := SequenceToInteger(w,r);

	// this check is not needed..
	if b in F then
		//continue;
	end if;

	TUP := TUP cat [<n,b>];
	F := F cat [n,b];
	end for;


	t := ZeroMatrix(GF(q),r^l,r^l);
	t[1][1] := 1;
	for j in [1..((r^l-1) div 2)] do
		a := TUP[j][1];
		b := TUP[j][2];
		t[a+1][j+1] := 1;
		t[b+1][j+1] := 1;

		t[a+1][((r^l - 1) div 2) + j + 1] := 1;
	
		// commented out so the code also works in characteristic two:
		// t[b+1][((r^l - 1) div 2) + j + 1] := -1;

		// (in odd characteristic, we can keep the above to get 
		// block diagonal matrices, i.e. direct sum)
	
	end for;


	V := [t^-1 * V[i] * t : i in [1..#V]];
	Vplus :=  [Submatrix(V[i], 1, 1, (r^l + 1) div 2, (r^l + 1) div 2) : i in [1..#V]];
	Vminus := [Submatrix(V[i], (r^l + 3) div 2, (r^l + 3) div 2, (r^l - 1) div 2, (r^l - 1) div 2) : i in [1..#V]];

	return hom<Sp(2*l,r) -> GL(r^l, q) | V>, hom<Sp(2*l,r) -> GL((r^l+1) div 2, q) | Vplus>, hom<Sp(2*l,r) -> GL((r^l-1) div 2, q) | Vminus>;

end intrinsic;
