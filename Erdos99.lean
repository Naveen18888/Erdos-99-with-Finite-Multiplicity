module

public import Mathlib
public import Erdos99.Part09CaplessFlaggedAndAssembly

/-!
# Erdős Problem 99 under finite multiplicity — main file

## What is proved

**Erdős Problem 99** asks: let `A ⊆ ℝ²` be a set of `n` points with minimum distance `1` whose
diameter is as small as possible among all such sets.  If `n` is sufficiently large, must `A`
contain three points forming an equilateral triangle of side `1`?

This development proves the following theorem (Theorem 1.1 of the manuscript
*"Erdős 99 under finite multiplicity"*), with **no `sorry` and no additional axioms**:

> **Theorem (`Erdos99.erdos99_finite_multiplicity`).**  There is `N` such that for every
> `n ≥ N` with `h(n) < ∞`, every optimal `n`-point configuration contains a unit equilateral
> triangle.

Here `h(n)` (the quantity of Erdős Problem 103) is the number of congruence classes of optimal
`n`-point configurations.  As a corollary:

> **Corollary (`Erdos99.erdos99_of_finite_multiplicity`).**  If `h(n) < ∞` for all sufficiently
> large `n`, then Erdős Problem 99 has a positive answer (`Erdos99.Erdos99Conjecture`).

**This is a conditional result.**  The hypothesis `h(n) < ∞` is *not* proved here (nor in the
manuscript), so this does **not** resolve Erdős Problem 99 unconditionally; nothing is claimed for
values of `n` with `h(n) = ∞`.

## The definitions used in the statements

All definitions are in `Erdos99/Part01Basics.lean`, section `Basic`; they are repeated here for
the reader's convenience (`Plane := EuclideanSpace ℝ (Fin 2)`, the Euclidean plane):

* `IsSeparated X  :=  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1 ≤ dist x y`
* `diam X  :=  Metric.diam (X : Set Plane)`
* `Admissible n X  :=  X.card = n ∧ IsSeparated X`
* `IsOptimal n X  :=  Admissible n X ∧ ∀ Y, Admissible n Y → diam X ≤ diam Y`
* `Congruent X Y  :=  ∃ e : Plane ≃ᵢ Plane, X.image e = Y`
* `numOptimalClasses n  :=  Set.encard {C | ∃ X, IsOptimal n X ∧ C = {Y | IsOptimal n Y ∧ Congruent X Y}}`
  — this is `h(n)`, the (possibly infinite, valued in `ℕ∞`) number of congruence classes of
  optimal configurations;
* `HasUnitTriangle X  :=  ∃ a ∈ X, ∃ b ∈ X, ∃ c ∈ X, dist a b = 1 ∧ dist b c = 1 ∧ dist a c = 1`
* `MinDistOne X  :=  IsSeparated X ∧ ∃ x ∈ X, ∃ y ∈ X, dist x y = 1`  (Erdős's normalisation)
* `IsErdosOptimal n X  :=  X.card = n ∧ MinDistOne X ∧
     ∀ Y, Y.card = n → MinDistOne Y → diam X ≤ diam Y`
* `Erdos99Conjecture  :=  ∀ᶠ n in atTop, ∀ X, IsErdosOptimal n X → HasUnitTriangle X`

`isErdosOptimal_iff_isOptimal` (section `Basic`) shows that for `n ≥ 2` the two notions of
optimality (minimum distance `≥ 1` versus exactly `1`) coincide.  The theorem
`erdos99_finite_multiplicity_explicit` at the end of this file restates Theorem 1.1 with
`IsOptimal`, `diam` and `HasUnitTriangle` unfolded, using only Mathlib notions (apart from `h(n)`).

## Layout of the formalization (ten files)

* `Erdos99.lean` (this file): the main theorem and its corollaries.
* `Erdos99/Part01Basics.lean`: definitions, §1, rhombi and tracks, planar faces, Euler's
  formula and Oler's inequality.
* `Erdos99/Part02LockingAndFans.lean`: pinned locking, the planar Minkowski inequality,
  Hilbert–Lorentz, polytopes and fans.
* `Erdos99/Part03LiftedFanAndDensity.lean`: the lifted fan theorem, first-order locking, the
  isodiametric and density estimates, annulus estimates.
* `Erdos99/Part04RoundnessAndConnectivity.lean`: roundness, connectivity of the contact graph,
  local capacity.
* `Erdos99/Part05FacesAndShores.lean`: faces, crosscuts, shores and short sources.
* `Erdos99/Part06TokensHopsCaps.lean`: tokens, hops, caps and exact counts.
* `Erdos99/Part07StabilityAndCharging.lean`: stability, the charging graph, pinned polynomials.
* `Erdos99/Part08Saturation.lean`: HH-adjacency, one-short faces and saturation.
* `Erdos99/Part09CaplessFlaggedAndAssembly.lean`: capless and flagged exclusions and the assembly
  of the track count.

Each part is divided into named sections (`section Name … end Name`); comments refer to these
sections by name.  Each file imports only Mathlib and earlier parts.

## Checking

`lake build` builds all ten files.  `#print axioms Erdos99.erdos99_finite_multiplicity` reports
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
-/

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- **The track count of §§3.4–5** (Lemma 3.4, Propositions 4.2–4.5, Proposition 5.6 and the
selection of §6, combined through equation (14)).  For every `ε, η > 0` there is a roundness defect
`ρ > 0` such that, eventually: for every centre `O` of a disc of radius `D/2 + η D` containing the
configuration which is also a centre of two-sided roundness with defect at most `ρ`, there is a cutoff
`0 ≤ L ≤ ε D` and a set `sel` of selected tracks (each with at least `L` rhombi) such that the
number `R` of tracks with at least `L` rhombi and `P = |sel|` satisfy
`R - P ≤ (3/5)(π D - P) + ε D`. -/
lemma track_count (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ O : Plane, (∀ x ∈ X, dist x O ≤ diam X / 2 + η * diam X) → IsRoundCentre ρ X O →
      ∃ L : ℝ, 0 ≤ L ∧ L ≤ ε * diam X ∧ ∃ sel ⊆ longTracks X L,
        (∀ T ∈ sel, IsSelectedTrack O (diam X) η T) ∧
        ((longTracks X L).card : ℝ) - sel.card ≤ 3 / 5 * (π * diam X - sel.card) + ε * diam X :=
  track_count_assembled ε η hε hη

/-- Sections 3.4–6 of the manuscript, from `track_count` (see `exists_countingWitness_of`). -/
lemma exists_countingWitness (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      Nonempty (CountingWitness X ε) :=
  exists_countingWitness_of_round track_count ε hε

/-- **Theorem 1.1 (finite-multiplicity assertion).** There is `N` such that for `n ≥ N` with
`h(n) < ∞`, every optimal `n`-point configuration contains a unit equilateral triangle.

This is a partial answer to Erdős Problem 99: nothing is claimed for `n` with `h(n) = ∞`. -/
theorem erdos99_finite_multiplicity :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → HasUnitTriangle X := by
  obtain ⟨ε, hε, hfin⟩ := final_contradiction
  filter_upwards [rhombi_card_lower ε hε, exists_countingWitness ε hε, rhombi_inside_card_le,
    eventually_ge_atTop 2] with n h1 h2 h3 hn2
  intro hfm X hX
  by_contra htri
  obtain ⟨w⟩ := h2 hfm X hX htri
  have hq := h1 hfm X hX htri
  have hD := hX.diam_pos hn2
  have hin := h3 hfm X hX htri (w.long \ w.sel) (Finset.sdiff_subset.trans w.long_subset)
  have hcard : ((w.long \ w.sel).card : ℝ) = (w.long.card : ℝ) - w.sel.card := by
    rw [Finset.card_sdiff_of_subset w.sel_subset, Nat.cast_sub (Finset.card_le_card w.sel_subset)]
  rw [hcard] at hin
  set L := (rhombi X).filter (fun R => ∃ T ∈ tracks X, T ∉ w.long ∧ Crosses T R)
  set Q := (rhombi X).filter (fun R => ∃ T ∈ w.sel, Crosses T R)
  set I := (rhombi X).filter (fun R => ∀ T ∈ tracks X, Crosses T R → T ∈ w.long \ w.sel)
  have hsub : rhombi X ⊆ L ∪ Q ∪ I := by
    intro R hR
    by_cases hL : ∃ T ∈ tracks X, T ∉ w.long ∧ Crosses T R
    · simp [L, hR, hL]
    by_cases hQ : ∃ T ∈ w.sel, Crosses T R
    · simp [Q, hR, hQ]
    refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hR, fun T hT hc => ?_⟩)
    refine Finset.mem_sdiff.2 ⟨?_, fun hs => hQ ⟨T, hs, hc⟩⟩
    by_contra hl
    exact hL ⟨T, hT, hl, hc⟩
  have hsplit : ((rhombi X).card : ℝ) ≤ L.card + Q.card + I.card := by
    have := (Finset.card_le_card hsub).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    exact_mod_cast this
  have hR := (abs_le.1 w.abs_R_sub).2
  refine hfin (diam X) (rhombi X).card w.long.card w.sel.card Q.card w.f w.β w.c₂ w.C₁ w.A hD hq
    (by linarith) w.f_add_c₂_le w.two_fifths (by exact_mod_cast w.C₁_le_c₂) (by positivity)
    (by positivity) (by exact_mod_cast Finset.card_le_card w.sel_subset)
    w.annular_linear w.annular_quadratic ?_
  have := w.short_loss
  linarith

/-- **Erdős Problem 99 under finite multiplicity.** If `h(n) < ∞` for all sufficiently large
`n`, then Erdős Problem 99 has a positive answer.  The hypothesis `h` is an open assumption: the
manuscript does not establish it, so this does not resolve Erdős Problem 99 unconditionally. -/
theorem erdos99_of_finite_multiplicity
    (h : ∀ᶠ n in atTop, numOptimalClasses n < ⊤) : Erdos99Conjecture := by
  filter_upwards [h, erdos99_finite_multiplicity, eventually_ge_atTop 2] with n hn hmain hn2
  intro X hX
  exact hmain hn X ((isErdosOptimal_iff_isOptimal hn2 X).1 hX)

end Erdos99

namespace Erdos99

/-- **Theorem 1.1, stated with the definitions unfolded.**  There is `N` such that for every
`n ≥ N` with `h(n) = numOptimalClasses n < ∞`: if `X` is a set of `n` points in the Euclidean plane
with all mutual distances at least `1`, and the diameter of `X` is at most the diameter of every
other such `n`-point set, then `X` contains three points at mutual distance exactly `1`. -/
theorem erdos99_finite_multiplicity_explicit :
    ∃ N : ℕ, ∀ n ≥ N, numOptimalClasses n < ⊤ →
      ∀ X : Finset (EuclideanSpace ℝ (Fin 2)),
        X.card = n →
        (∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1 ≤ dist x y) →
        (∀ Y : Finset (EuclideanSpace ℝ (Fin 2)), Y.card = n →
          (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → 1 ≤ dist x y) →
          Metric.diam (X : Set (EuclideanSpace ℝ (Fin 2))) ≤
            Metric.diam (Y : Set (EuclideanSpace ℝ (Fin 2)))) →
        ∃ a ∈ X, ∃ b ∈ X, ∃ c ∈ X, dist a b = 1 ∧ dist b c = 1 ∧ dist a c = 1 := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 erdos99_finite_multiplicity
  exact ⟨N, fun n hn hfin X hcard hsep hmin =>
    hN n hn hfin X ⟨⟨hcard, hsep⟩, fun Y hY => hmin Y hY.1 hY.2⟩⟩

end Erdos99

end

#print axioms Erdos99.erdos99_finite_multiplicity
#print axioms Erdos99.erdos99_finite_multiplicity_explicit
#print axioms Erdos99.erdos99_of_finite_multiplicity
