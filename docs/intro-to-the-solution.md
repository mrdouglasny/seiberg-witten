# The Seiberg–Witten solution — a short introduction

A self-contained overview of the solution, oriented toward the Lean formalization.
For the original papers and reviews see [`refs/README.md`](refs/README.md); for the
conceptual framing (why this is the canonical "foundations for physical reasoning"
example) see [`foundations-for-physical-reasoning.md`](foundations-for-physical-reasoning.md).

## 1. The setup

Pure `N=2` `SU(2)` super Yang–Mills has a complex adjoint scalar `φ`. Generic `⟨φ⟩`
breaks `SU(2) → U(1)`, leaving a one-complex-dimensional **Coulomb branch** of vacua,
gauge-invariantly parametrized by
```
u = ⟨Tr φ²⟩.
```
At low energy the theory is an abelian `N=2` `U(1)` gauge theory. `N=2` supersymmetry
forces its entire two-derivative action to be encoded in **one holomorphic function**, the
**prepotential** `F(a)`, where `a` is the `N=2` special coordinate (the scalar in the
`U(1)` vector multiplet). The effective coupling and the Kähler metric are
```
τ(a) = F''(a),      ds² = Im τ \, da\, d\bar a ,
```
and a **dual** coordinate is `a_D = F'(a) = ∂F/∂a`. Electric–magnetic duality acts on
`(a_D, a)` by `Sp(2,ℤ) = SL(2,ℤ)`.

## 2. The problem

Perturbatively `F` is **one-loop exact** (an `N=2` non-renormalization theorem),
```
F_pert(a) = (i/2π)\, a² \ln(a²/Λ²),
```
but there are infinitely many **instanton** corrections `F_inst = a² Σ_{k≥1} c_k (Λ/a)^{4k}`.
Computing them directly is hopeless; the `c_k` are what an exact solution must deliver.

## 3. The strategy (the "lore")

Three physical inputs pin `F` down without summing instantons:

1. **Holomorphy** — `F` is holomorphic; `Im τ > 0` (positivity of the metric) cannot hold
   globally on the `u`-plane, so `a(u)` must be multivalued, i.e. the `u`-plane carries
   **monodromy**.
2. **Singularities** — the metric degenerates exactly where a BPS state becomes massless
   (`M ∝ |n_e a + n_m a_D| → 0`). For pure `SU(2)` there are precisely **three**: weak
   coupling `u→∞`, and two strong-coupling points `u = ±Λ²` where a **monopole** `(n_e,n_m)=(0,1)`
   and a **dyon** `(1,1)` become massless.
3. **Duality / monodromy consistency** — the monodromies around the singular points are
   `SL(2,ℤ)` matrices acting on `(a_D, a)`, fixed by the light state at each point, and
   they must compose: `M_∞ = M_{Λ²}\, M_{−Λ²}`.

Holomorphy + exactly these singularities + matching the weak-coupling asymptotics of
input (2) **uniquely determine** `a(u)` and `a_D(u)`.

## 4. The solution

`(a_D, a)` are realized as **periods of a meromorphic one-form `λ_SW`** on a family of
**elliptic curves** fibered over the `u`-plane:
```
a = ∮_A λ_SW ,    a_D = ∮_B λ_SW ,    τ = ∂a_D/∂a = period ratio of the curve.
```
The curve's complex-structure modulus *is* the effective coupling `τ`; its degenerations
sit exactly at `u = ±Λ²`, reproducing the required monodromies. The prepotential follows
by integrating `a_D = ∂F/∂a`. Expanding the periods at large `u` reproduces
`F_pert + F_inst` — and the instanton coefficients `c_k` so obtained were **later matched
exactly** by Nekrasov's instanton partition function (proved by Nekrasov–Okounkov,
Nakajima–Yoshioka). That independent agreement is the validation.

## 5. Generalizations

- **Matter** (SW2, [hep-th/9408099](https://arxiv.org/abs/hep-th/9408099)): `N_f ≤ 4`
  flavors; bare masses become **residues of `λ_SW`**; `N_f = 4` is superconformal with
  exact `SL(2,ℤ)` duality.
- **`SU(N)`** (KLYT, Argyres–Faraggi): the **hyperelliptic** curve
  ```
  y² = P_N(x)² − Λ^{2N},     P_N(x) = ∏ (x − φ_i),     genus = N − 1,
  ```
  with `a_i, a_{D,i}` the periods and `τ_{ij} = ∂²F/∂a_i∂a_j` the period matrix.

## 6. What the formalization does with this

| Solution ingredient | Lean status (this repo) |
|---|---|
| `SU(N)` curve `y²=P_N²−Λ^{2N}`, `genus = N−1` | ✅ Phase 0, axiom-clean (via `jacobian-challenge`) |
| holomorphic differentials, period matrix `τ ∈ Siegel`, `τ=τᵀ`, `Im τ ≻ 0` | 🔶 Phase 1 (`SU(2)` axiom-free) |
| `λ_SW`, periods `a, a_D`, `a_D=∂F/∂a`, masses = residues | 🔬 Phase 2 (meromorphic/mass layer) |
| singular locus, Argyres–Douglas, Picard–Fuchs (asymptotics) | 🔬 Phase 3 (links `picard-lefschetz`) |
| monodromy `Sp(2(N−1),ℤ)`, BPS spectrum | 🔬 Phase 4 (stretch) |

The **proved** rows are rigorous mathematics. The **physical inputs** of §3 —
holomorphy, the exact set of singularities, duality, asymptotic matching — are the
*codified lore*: stated as explicit, vetted axioms and tracked in `AXIOM_AUDIT.md` /
`formalization.yaml`, with the Nekrasov / monodromy / numeric-period cross-checks as the
independent-agreement validation.
