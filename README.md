# Gm-Reduce

### About

`Gm-Reduce` is a Magma package that, given a curve over a number field together with a finite degree map to the projective line, computes a small (possibly singular) affine plane model of the curve and map.

Given an affine plane model $C: f(t,x) = 0$ of a curve over a number field $K$, we determine constants $a,b,c \in K$ such that the rescaled equation $c f(at,bx) = 0$ has small coefficients. This is done using linear and quadratic programming.

---

### Installation

To use `Gm-Reduce`, you must already have Magma installed on your system.

1.  Clone this repository to your local machine.
2.  Load the package in your Magma session by navigating to the directory, starting Magma, and then attaching the spec file.
```
AttachSpec("spec");
```


---

### Usage

The top-level intrinsics are `BestModel` and `AllReducedModels`, both of which take as input a rational function on a curve, of type `FldFunFracSchElt`. We illustrate the basic usage below.

**Example:**

```
// Magma code for Belyi map with label 4T5-4_4_3.1-a
> AttachSpec("spec");
> K<nu> := RationalsAsNumberField(); // Define the base field
> S<x> := PolynomialRing(K); // Define the curve
> X := EllipticCurve(x^3 + 47/48*x + 2359/864,S!0);
> KX<x,y> := FunctionField(X); // Define the map
> phi := (139968*x^2 - 23328*x + 490860 + 279936*y)/(12*x-13)^4;
> BestModel(phi);

-t^2*x^4 + 8*t*x - 6*t - 4*x + 3
1/2
```

---

### Contributing

Contributions are welcome! If you have suggestions or find any bugs, please open an issue or submit a pull request.
