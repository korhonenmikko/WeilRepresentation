# WeilRepresentation
MAGMA package for computing Weil representations of G = Sp(2l,r). Here r is a power of some odd prime.

The intrinsic ```WeilRepresentation``` constructs the Weil representation of Sp(2l,r) over the finite field GF(q). This representation has degree r^l and exists when the prime divisor of r divides q-1. The representation is returned as a homomorphism Sp(2l,r) -> GL(r^l, q).

If q is odd, then the Weil representation is a direct sum of two irreducible representations, of degrees (r^l+1)/2 and (r^l-1)/2. These are constructed with the instrinsic ```IrreducibleWeilRepresentation```. This also works for q even, but in this case the Weil representation is not a direct sum, and only the representation of degree (r^l-1)/2 is irreducible.

# Files and usage

Information on working with MAGMA spec files and packages can be found here: [http://magma.maths.usyd.edu.au/magma/handbook/text/24](http://magma.maths.usyd.edu.au/magma/handbook/text/24).

The package contains the following files:

```
WeilRepresentation.spec
WeilRepresentation.m
```

Place all of these files in the same folder. Then to load the package in MAGMA, use the command ```AttachSpec``` to load the package. 

For example, if ```WeilRepresentation.spec``` is in the current working directory, the command

```
AttachSpec("WeilRepresentation.spec");
```

loads the package.

# Example

```
// f: Weil representation of Sp(2,25) over GF(11)
f := WeilRepresentation(1,25,11);

// f1,f2,f3 are representations of Sp(4,3) over GF(7).
// f1: Weil representation of degree 9.
// f2: Irreducible Weil representation of degree 5.
// f3: Irreducible Weil representation of degree 4.
f1,f2,f3 := IrreducibleWeilRepresentation(2, 3, 7);

```
