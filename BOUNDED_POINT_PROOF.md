# The bounded-point-orbit correction

The final entire-function statement assumes

```lean
(hbounded : Bornology.IsBounded (Set.range (fun n : ℕ => (f^[n]) z)))
```

for z in the initial Fatou component. It does not assume a bound on whole
Fatou components. As before, it is conditional on `ClassicalHyperbolicMetrics`,
with curvature −1. The local Challenge theorem retains its previous hypotheses.

## 1. A bounded neighbourhood of the marked point

Assume the Fatou components U_n are pairwise disjoint. Choose two distinct
points a,b in U_0 and a small disc B about z contained in U_0. Every positive
iterate maps B into U_n and hence omits a and b. The values f^n(z) are bounded.
After normalising the omitted values to 0 and 1, Schottky's estimate bounds
all positive iterates uniformly on a smaller concentric disc. The identity
iterate is bounded there too. Thus, for some R>0, z lies in the interior of

    {w : every f^n(w) belongs to B(0,R)}.

This is `AreaDeficit.bounded_point_mem_trapped_interior` in
`BoundedWanderingDomains/PointOrbitBridge.lean`.

## 2. Auxiliary trapped components

Let V=B(0,R+2), let T be the interior of the set of points whose iterates all
stay in V, and let W_n be the component of T containing f^n(z).
The entire nonconstant map is open, so T is forward invariant. Its iterates
are locally uniformly bounded, so T is contained in the Fatou set. Hence
W_n is contained in U_n. In particular, the W_n are pairwise disjoint and
f(W_n) is contained in W_{n+1}. Every centre f^n(z) has norm at most R.

The interiors of the trapped sets for B(0,R+2) and its closed disc coincide.
Indeed, every iterate is open: the image of the interior of the closed-disc
trapped set is an open subset of the closed disc, hence lies in the open
disc. Maximum modulus rules out bounded complementary components of the
closed-disc trapped set. The supplied planar topology theorem therefore
makes each W_n simply connected. No compact containment of the whole W_n
in a smaller subdomain of V is asserted.

The open/closed-disc equality is `trapped_ball_interior_eq_closed`.
The maximum-modulus and topology arguments are in `TrappedSimpleConnectivity.lean`.
Their assembly with the Fatou-component inclusions is in `BoundedPointWandering.lean`.

## 3. Fixed intrinsic discs shrink

Choose a Riemann chart u_n:W_n→D with u_n(f^n(z))=0. For each fixed 0<r<1,
write D_n(r)=u_n^{-1}(B(0,r)). The inverse charts have pairwise disjoint,
uniformly bounded images. The previously proved shrinking-images theorem
therefore gives

    sup { |w-f^n(z)| : w in D_n(r) } → 0.

Consequently D_n(r) is eventually contained in K=closed B(0,R+1).
The time may depend on r, but K is independent of r.
These statements are proved in `ShrinkingChartDiscs.lean`.

## 4. Eventual injectivity from local branches

Cover K by finitely many open neighbourhoods O_j with univalent local
coordinates ψ_j in which

    f(w)=c_j+ψ_j(w)^{d_j},   d_j≥1.

Such coordinates exist at every point of a nonconstant holomorphic map,
including critical points. A Lebesgue number for this finite cover, together
with shrinking, ensures that every sufficiently late D_n(r) lies in some O_j.
Because the W_n are pairwise disjoint, their sufficiently late members omit
all the finitely many values c_j.

On the simply connected successor domain W_{n+1}, choose a holomorphic root
h of w-c_j of order d_j. It is nowhere zero. On the connected set D_n(r),

    q(w)=ψ_j(w)/h(f(w))

is continuous and satisfies q(w)^{d_j}=1. Its image lies in a finite set,
so q is constant. If f(x)=f(y) for x,y in D_n(r), this identity gives
ψ_j(x)=ψ_j(y), and injectivity of ψ_j gives x=y.

This is the required local inverse-branch argument. It does not require
avoidance of the global singular set of the entire function. The only
values omitted here are the finitely many branch values of the chosen local
coordinate neighbourhoods.

The key lemmas are `injOn_of_power_coordinate` and
`eventually_injOn_shrinking_chart_discs` in `LocalDiscInjectivity.lean`.

## 5. The area contradiction

For each fixed r, choose a starting time after both compact containment in K
and injectivity hold. Schwarz's lemma gives f(D_n(r))⊆D_{n+1}(r). Since their
successor domains are disjoint, f is injective on the union of the tail discs.
The existing local area argument gives a bound for the hyperbolic area of
the initial tail disc which depends on f,V,K but not on r or the chosen time.

For curvature −1, the area of D_n(r) is

    4π r²/(1-r²).

It tends to infinity as r tends to 1, a contradiction. The uniform bound
needed here is proved in `EventualCompactDiscs.lean`; its quantifiers
explicitly permit the starting time to depend on r.

`BoundedPointWandering.lean` proves the assembled theorem.
`Solution.lean` converts the Mathlib bounded-set hypothesis to a numerical
orbit bound and supplies the metric input. Neither simple connectivity nor
eventual injectivity is a hypothesis of the entire Challenge statement.
