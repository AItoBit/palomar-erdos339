module

public import Mathlib

/-!
# Erdős Problem 339 — supplied proof development

Packaging note (6 October 2026): this development has not been compiled or
checked with Comparator in the packaging environment. The proof claims below
require verification before submission. No mathematical novelty is claimed.

Let `A ⊆ ℕ` be a basis of order `r`. Must the set of integers representable as the sum of
exactly `r` distinct elements from `A` have positive lower density?

Answer: yes (Hegyvári–Hennecart–Plagne, J. reine angew. Math. 560 (2003), 199–220).
Main theorem: `Erdos339.erdos_339`. Variants: `erdos_339_exact`, `erdos_339_upper`,
`erdos_339_upper_exact`. See `ERDOS_339.md` for the source audit and fidelity table.
-/

@[expose] public section


/-!
# Erdős Problem 339 — definitions used in the statement

Source: <https://www.erdosproblems.com/339> (problem text from [ErGr80, p. 52]) and the
site's definitions page <https://www.erdosproblems.com/definitions>.

* A set `A ⊆ ℕ` is an *additive basis of order `r`* if all sufficiently large integers are the
  sum of at most `r` integers from `A` (repetitions allowed).
* The *lower density* of `S ⊆ ℕ` is `liminf_{N → ∞} |S ∩ {1, …, N}| / N`.
-/


namespace Erdos339

open Filter

/-- The set of integers that are the sum of at most `r` elements of `A`, repetitions allowed
(a multiset of at most `r` elements of `A`; the empty sum `0` is included). -/
def sumsAtMost (r : ℕ) (A : Set ℕ) : Set ℕ :=
  {n | ∃ m : Multiset ℕ, Multiset.card m ≤ r ∧ (∀ a ∈ m, a ∈ A) ∧ m.sum = n}

/-- `A ⊆ ℕ` is an additive basis of order `r` (erdosproblems.com convention): every sufficiently
large natural number is the sum of at most `r` elements of `A` (repetitions allowed). -/
def IsAddBasisOfOrder (A : Set ℕ) (r : ℕ) : Prop :=
  ∀ᶠ n in atTop, n ∈ sumsAtMost r A

/-- The set of integers representable as the sum of exactly `r` pairwise distinct elements of
`A`, i.e. sums `∑ s ∈ S, s` over finite sets `S ⊆ A` with exactly `r` elements. -/
def distinctSums (r : ℕ) (A : Set ℕ) : Set ℕ :=
  {n | ∃ S : Finset ℕ, S.card = r ∧ (↑S : Set ℕ) ⊆ A ∧ ∑ s ∈ S, s = n}

open Classical in
/-- The counting function `|S ∩ {1, …, N}|`. -/
noncomputable def countUpTo (S : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (· ∈ S)).card

/-- Lower (natural) density `liminf_{N → ∞} |S ∩ {1, …, N}| / N`, as a real number.
The sequence takes values in `[0, 1]`, so this `liminf` is the genuine one. -/
noncomputable def lowerDensity (S : Set ℕ) : ℝ :=
  liminf (fun N : ℕ => (countUpTo S N : ℝ) / N) atTop

/-- Upper (natural) density `limsup_{N → ∞} |S ∩ {1, …, N}| / N`, as a real number. -/
noncomputable def upperDensity (S : Set ℕ) : ℝ :=
  limsup (fun N : ℕ => (countUpTo S N : ℝ) / N) atTop

end Erdos339


/-!
# Erdős Problem 339 — the finite counting argument

For a set `A ⊆ ℕ` and `r : ℕ`, write `rA ∩ [0, N)` for the sums of `r`-tuples of elements of `A`
below `N` and `r^A` for the sums of `r` distinct elements. We prove
`|rA ∩ [0, N)| ≤ (1 + r(r+1))^r · |r^A ∩ [0, 2^r N)|` whenever `A ∩ [0, N)` has at least
`r + 1` elements, by making the coordinates of a representing tuple distinct from all other
coordinates one at a time.
-/


namespace Erdos339

open Finset

open Classical

/-! ### An abstract counting lemma -/

/-- If every `b ∈ B` forbids at most `k` partners `F b`, and `X` has more than `k` elements,
then the number of sums `b + x` (`b ∈ B`, `x ∈ X`) is at most `1 + k(k+1)` times the number of
*allowed* sums `b + x` (`x ∉ F b`). -/
lemma card_sums_le_allowed (B X : Finset ℕ) (F : ℕ → Finset ℕ) (k : ℕ)
    (hF : ∀ b ∈ B, (F b).card ≤ k) (hX : k + 1 ≤ X.card) :
    (B.biUnion fun b => X.image (b + ·)).card ≤
      (1 + k * (k + 1)) * (B.biUnion fun b => (X \ F b).image (b + ·)).card := by
  set allowed := B.biUnion fun b => (X \ F b).image (b + ·) with hallowed
  set bad := B.biUnion fun b => (F b).image (b + ·) with hbad
  have hsub : (B.biUnion fun b => X.image (b + ·)) ⊆ allowed ∪ bad := by
    intro y hy
    simp only [mem_biUnion, mem_image] at hy
    obtain ⟨b, hb, x, hx, rfl⟩ := hy
    by_cases hxF : x ∈ F b
    · exact mem_union_right _ (mem_biUnion.2 ⟨b, hb, mem_image.2 ⟨x, hxF, rfl⟩⟩)
    · exact mem_union_left _ (mem_biUnion.2 ⟨b, hb, mem_image.2 ⟨x, mem_sdiff.2 ⟨hx, hxF⟩, rfl⟩⟩)
  have hbadcard : bad.card ≤ B.card * k :=
    card_biUnion_le_card_mul _ _ _ fun b hb => card_image_le.trans (hF b hb)
  obtain ⟨T, hTX, hTcard⟩ := exists_subset_card_eq hX
  have hcover : B ⊆ T.biUnion fun t => B.filter fun b => t ∉ F b := by
    intro b hb
    have hns : ¬ T ⊆ F b := by
      intro h
      have := (card_le_card h).trans (hF b hb)
      omega
    obtain ⟨t, htT, htF⟩ := not_subset.1 hns
    exact mem_biUnion.2 ⟨t, htT, mem_filter.2 ⟨hb, htF⟩⟩
  have hBcard : B.card ≤ (k + 1) * allowed.card := by
    calc B.card ≤ (T.biUnion fun t => B.filter fun b => t ∉ F b).card := card_le_card hcover
      _ ≤ T.card * allowed.card := by
        apply card_biUnion_le_card_mul
        intro t ht
        apply card_le_card_of_injOn (fun b => b + t)
        · intro b hb
          have hb' := mem_filter.1 hb
          exact mem_biUnion.2 ⟨b, hb'.1, mem_image.2 ⟨t, mem_sdiff.2 ⟨hTX ht, hb'.2⟩, rfl⟩⟩
        · intro a _ b _ hab
          simpa using hab
      _ = (k + 1) * allowed.card := by rw [hTcard]
  calc _ ≤ (allowed ∪ bad).card := card_le_card hsub
    _ ≤ allowed.card + bad.card := card_union_le _ _
    _ ≤ allowed.card + (k + 1) * allowed.card * k := by
        have := Nat.mul_le_mul_right k hBcard
        omega
    _ = (1 + k * (k + 1)) * allowed.card := by ring

/-! ### Representations isolated on a set of coordinates -/

/-- `n` is the sum of an `r`-tuple of elements of `A` whose coordinates in `s` are distinct
from every other coordinate. -/
def IsoRep (A : Set ℕ) (r : ℕ) (s : Finset (Fin r)) (n : ℕ) : Prop :=
  ∃ f : Fin r → ℕ, (∀ j, f j ∈ A) ∧ (∀ i ∈ s, ∀ j, f j = f i → j = i) ∧ ∑ j, f j = n

/-- Number of `n < N` with an `s`-isolated representation. -/
noncomputable def isoCount (A : Set ℕ) (r : ℕ) (s : Finset (Fin r)) (N : ℕ) : ℕ :=
  ((range N).filter (IsoRep A r s)).card

/-- Number of elements of `S` below `N`. -/
noncomputable def countBelow (S : Set ℕ) (N : ℕ) : ℕ :=
  ((range N).filter (· ∈ S)).card

lemma countBelow_mono (S : Set ℕ) {M N : ℕ} (h : M ≤ N) : countBelow S M ≤ countBelow S N := by
  apply card_le_card
  intro n hn
  simp only [mem_filter, mem_range] at hn ⊢
  exact ⟨by omega, hn.2⟩

lemma isoCount_mono (A : Set ℕ) (r : ℕ) (s : Finset (Fin r)) {M N : ℕ} (h : M ≤ N) :
    isoCount A r s M ≤ isoCount A r s N := by
  apply card_le_card
  intro n hn
  simp only [mem_filter, mem_range] at hn ⊢
  exact ⟨by omega, hn.2⟩

/-- One isolation step: making coordinate `i` distinct from all others costs a factor
`1 + r(r+1)` in the count and doubles the range. -/
lemma isoCount_step (A : Set ℕ) (r : ℕ) (s : Finset (Fin r)) (i : Fin r) (N : ℕ)
    (hX : r + 1 ≤ countBelow A N) :
    isoCount A r s N ≤ (1 + r * (r + 1)) * isoCount A r (insert i s) (2 * N) := by
  -- the "bases": sums of all coordinates but the `i`-th of an `s`-isolated tuple
  let Bp : ℕ → Prop := fun b => ∃ g : Fin r → ℕ, (∀ j, g j ∈ A) ∧
    (∀ k ∈ s, ∀ j, g j = g k → j = k) ∧ ∑ j ∈ univ.erase i, g j = b
  let B : Finset ℕ := (range N).filter Bp
  let g : ℕ → Fin r → ℕ := fun b => if h : Bp b then Classical.choose h else fun _ => 0
  have hg : ∀ b, Bp b → (∀ j, g b j ∈ A) ∧ (∀ k ∈ s, ∀ j, g b j = g b k → j = k) ∧
      ∑ j ∈ univ.erase i, g b j = b := by
    intro b hb
    simp only [g, hb, ↓reduceDIte]
    exact Classical.choose_spec hb
  let F : ℕ → Finset ℕ := fun b => univ.image (g b)
  let X : Finset ℕ := (range N).filter (· ∈ A)
  have hF : ∀ b ∈ B, (F b).card ≤ r := fun b _ =>
    card_image_le.trans (by simp)
  have hXc : r + 1 ≤ X.card := hX
  have h1 : (range N).filter (IsoRep A r s) ⊆ B.biUnion fun b => X.image (b + ·) := by
    intro n hn
    simp only [mem_filter, mem_range] at hn
    obtain ⟨hnN, f, hfA, hfs, hfsum⟩ := hn
    have hsplit := sum_erase_add univ f (mem_univ i)
    rw [hfsum] at hsplit
    refine mem_biUnion.2 ⟨∑ j ∈ univ.erase i, f j, ?_, mem_image.2 ⟨f i, ?_, hsplit⟩⟩
    · exact mem_filter.2 ⟨mem_range.2 (by omega), f, hfA, hfs, rfl⟩
    · exact mem_filter.2 ⟨mem_range.2 (by omega), hfA i⟩
  have h2 : (B.biUnion fun b => (X \ F b).image (b + ·)) ⊆
      (range (2 * N)).filter (IsoRep A r (insert i s)) := by
    intro y hy
    simp only [mem_biUnion, mem_image] at hy
    obtain ⟨b, hb, x, hx, rfl⟩ := hy
    obtain ⟨hbN, hbp⟩ := mem_filter.1 hb
    obtain ⟨hxX, hxF⟩ := mem_sdiff.1 hx
    obtain ⟨hxN, hxA⟩ := mem_filter.1 hxX
    rw [mem_range] at hbN hxN
    obtain ⟨hgA, hgs, hgsum⟩ := hg b hbp
    have hxne : ∀ j, g b j ≠ x := by
      intro j hj
      exact hxF (mem_image.2 ⟨j, mem_univ _, hj⟩)
    refine mem_filter.2 ⟨mem_range.2 (by omega), Function.update (g b) i x, ?_, ?_, ?_⟩
    · intro j
      by_cases hji : j = i
      · subst hji; simpa using hxA
      · simpa [Function.update_of_ne hji] using hgA j
    · intro k hk j hjk
      rcases mem_insert.1 hk with rfl | hks
      · by_contra hne
        rw [Function.update_of_ne hne, Function.update_self] at hjk
        exact hxne j hjk
      · by_cases hki : k = i
        · subst hki
          by_contra hne
          rw [Function.update_of_ne hne, Function.update_self] at hjk
          exact hxne j hjk
        · rw [Function.update_of_ne hki] at hjk
          by_cases hji : j = i
          · subst hji
            rw [Function.update_self] at hjk
            exact absurd hjk.symm (hxne k)
          · rw [Function.update_of_ne hji] at hjk
            exact hgs k hks j hjk
    · have he : ∑ j ∈ univ.erase i, Function.update (g b) i x j = ∑ j ∈ univ.erase i, g b j :=
        sum_congr rfl fun j hj => Function.update_of_ne (ne_of_mem_erase hj) _ _
      rw [← sum_erase_add univ _ (mem_univ i), Function.update_self, he, hgsum]
  calc isoCount A r s N ≤ (B.biUnion fun b => X.image (b + ·)).card := card_le_card h1
    _ ≤ (1 + r * (r + 1)) * (B.biUnion fun b => (X \ F b).image (b + ·)).card :=
        card_sums_le_allowed B X F r hF hXc
    _ ≤ (1 + r * (r + 1)) * isoCount A r (insert i s) (2 * N) :=
        Nat.mul_le_mul_left _ (card_le_card h2)

/-- Iterating the isolation step over a set `s` of coordinates. -/
lemma isoCount_iter (A : Set ℕ) (r : ℕ) (N : ℕ) (hX : r + 1 ≤ countBelow A N)
    (s : Finset (Fin r)) :
    isoCount A r ∅ N ≤ (1 + r * (r + 1)) ^ s.card * isoCount A r s (2 ^ s.card * N) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hM : N ≤ 2 ^ s.card * N := Nat.le_mul_of_pos_left N (by positivity)
    have hstep := isoCount_step A r s i (2 ^ s.card * N) (hX.trans (countBelow_mono A hM))
    rw [card_insert_of_notMem hi]
    calc isoCount A r ∅ N ≤ (1 + r * (r + 1)) ^ s.card * isoCount A r s (2 ^ s.card * N) := ih
      _ ≤ (1 + r * (r + 1)) ^ s.card *
            ((1 + r * (r + 1)) * isoCount A r (insert i s) (2 * (2 ^ s.card * N))) :=
          Nat.mul_le_mul_left _ hstep
      _ = _ := by rw [pow_succ, pow_succ]; ring_nf

/-- A fully isolated representation is a representation by `r` distinct elements. -/
lemma isoRep_univ_imp (A : Set ℕ) (r n : ℕ) (h : IsoRep A r univ n) : n ∈ distinctSums r A := by
  obtain ⟨f, hfA, hfs, hsum⟩ := h
  have hinj : Function.Injective f := fun a b hab => hfs b (mem_univ _) a hab
  refine ⟨univ.image f, ?_, ?_, ?_⟩
  · rw [card_image_of_injective _ hinj]; simp
  · intro x hx
    obtain ⟨j, rfl⟩ : ∃ j, f j = x := by simpa using hx
    exact hfA j
  · rw [sum_image (fun a _ b _ hab => hinj hab)]; exact hsum

/-- **Main finite inequality.** -/
theorem isoCount_le_distinct (A : Set ℕ) (r N : ℕ) (hX : r + 1 ≤ countBelow A N) :
    isoCount A r ∅ N ≤
      (1 + r * (r + 1)) ^ r * countBelow (distinctSums r A) (2 ^ r * N) := by
  have h := isoCount_iter A r N hX univ
  simp only [card_univ, Fintype.card_fin] at h
  refine h.trans (Nat.mul_le_mul_left _ (card_le_card ?_))
  intro n hn
  simp only [mem_filter] at hn ⊢
  exact ⟨hn.1, isoRep_univ_imp A r n hn.2⟩

end Erdos339


/-!
# Erdős Problem 339

Let `A ⊆ ℕ` be a basis of order `r`. Must the set of integers representable as the sum of
exactly `r` distinct elements from `A` have positive lower density?

Answer: yes (Hegyvári–Hennecart–Plagne, J. reine angew. Math. 560 (2003), 199–220).
-/


namespace Erdos339

open Finset Filter

open Classical

/-! ### Elementary consequences of the basis hypothesis -/

lemma basis_infinite {A : Set ℕ} {r : ℕ} (hA : IsAddBasisOfOrder A r) : A.Infinite := by
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hA
  intro hfin
  obtain ⟨M, hM⟩ := hfin.bddAbove
  obtain ⟨m, hcard, hmA, hsum⟩ := hN0 (N0 + r * M + 1) (by omega)
  have h1 := Multiset.sum_le_card_nsmul m M (fun x hx => hM (hmA x hx))
  rw [hsum, smul_eq_mul] at h1
  have h2 := Nat.mul_le_mul_right M hcard
  omega

lemma basis_order_pos {A : Set ℕ} {r : ℕ} (hA : IsAddBasisOfOrder A r) : 1 ≤ r := by
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hA
  by_contra h
  obtain ⟨m, hcard, -, hsum⟩ := hN0 (N0 + 1) (by omega)
  have : m = 0 := Multiset.card_eq_zero.1 (by omega)
  subst this
  simp at hsum

lemma exists_tuple_of_list (l : List ℕ) (r : ℕ) (h : l.length = r) :
    ∃ f : Fin r → ℕ, (∀ j, f j ∈ l) ∧ ∑ j, f j = l.sum := by
  subst h
  exact ⟨fun j => l[j], fun j => List.getElem_mem _, by rw [← List.sum_ofFn]; simp⟩

/-- A sum of at most `r` elements of `A` is a sum of an `r`-tuple of elements of `A ∪ {0}`. -/
lemma isoRep_empty_of_multiset (A : Set ℕ) (r : ℕ) (m : Multiset ℕ)
    (hcard : Multiset.card m ≤ r) (hmA : ∀ a ∈ m, a ∈ A) :
    IsoRep (insert 0 A) r ∅ m.sum := by
  set l : List ℕ := m.toList ++ List.replicate (r - Multiset.card m) 0 with hl
  have hlen : l.length = r := by simp [hl]; omega
  have hlsum : l.sum = m.sum := by simp [hl]
  obtain ⟨f, hfl, hfsum⟩ := exists_tuple_of_list l r hlen
  refine ⟨f, ?_, by simp, by rw [hfsum, hlsum]⟩
  intro j
  have hmem := hfl j
  rw [hl, List.mem_append] at hmem
  rcases hmem with h | h
  · exact Set.mem_insert_of_mem _ (hmA _ (Multiset.mem_toList.1 h))
  · rw [List.eq_of_mem_replicate h]; exact Set.mem_insert _ _

/-- Removing the possible summand `0`: a sum of `r` distinct elements of `A ∪ {0}`, shifted by
some element of `{0} ∪ T`, is a sum of `r` distinct elements of `A`. -/
lemma distinct_shift (A : Set ℕ) (r : ℕ) (hr : 1 ≤ r) (T : Finset ℕ) (hT : (↑T : Set ℕ) ⊆ A)
    (hTc : T.card = r) (n : ℕ) (hn : n ∈ distinctSums r (insert 0 A)) :
    ∃ t ∈ insert 0 T, n + t ∈ distinctSums r A := by
  obtain ⟨S, hSc, hSA, rfl⟩ := hn
  by_cases h : 0 ∈ S ∧ 0 ∉ A
  · obtain ⟨h0S, h0A⟩ := h
    have hcard : (S.erase 0).card = r - 1 := by rw [card_erase_of_mem h0S, hSc]
    have hns : ¬ T ⊆ S.erase 0 := by
      intro hsub
      have := card_le_card hsub
      omega
    obtain ⟨t, htT, htS⟩ := not_subset.1 hns
    have htA : t ∈ A := hT htT
    refine ⟨t, mem_insert_of_mem htT, insert t (S.erase 0), ?_, ?_, ?_⟩
    · rw [card_insert_of_notMem htS, hcard]; omega
    · intro x hx
      rcases mem_insert.1 (mem_coe.1 hx) with rfl | hx
      · exact htA
      · obtain ⟨hx0, hxS⟩ := mem_erase.1 hx
        rcases hSA hxS with h | h
        · exact absurd h hx0
        · exact h
    · rw [sum_insert htS, sum_erase S (f := fun x => x) rfl, add_comm]
  · refine ⟨0, mem_insert_self _ _, S, hSc, ?_, by simp⟩
    intro x hx
    rcases hSA hx with h0 | h0
    · subst h0
      by_contra hA0
      exact h ⟨hx, hA0⟩
    · exact h0

/-- Counting through a bounded shift. -/
lemma countBelow_shift (S D : Set ℕ) (U : Finset ℕ) (c M : ℕ) (hc : ∀ t ∈ U, t < c)
    (h : ∀ n ∈ S, ∃ t ∈ U, n + t ∈ D) :
    countBelow S M ≤ U.card * countBelow D (M + c) := by
  unfold countBelow
  have hsub : (range M).filter (· ∈ S) ⊆
      U.biUnion fun t => ((range M).filter (· ∈ S)).filter fun n => n + t ∈ D := by
    intro n hn
    obtain ⟨t, htU, htD⟩ := h n (mem_filter.1 hn).2
    exact mem_biUnion.2 ⟨t, htU, mem_filter.2 ⟨hn, htD⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le_card_mul _ _ _ ?_)
  intro t ht
  apply card_le_card_of_injOn (fun n => n + t)
  · intro n hn
    rw [mem_coe, mem_filter, mem_filter, mem_range] at hn
    rw [mem_coe, mem_filter, mem_range]
    exact ⟨show n + t < M + c by have := hc t ht; omega, hn.2⟩
  · intro a _ b _ hab
    simpa using hab

lemma countBelow_le_countUpTo (S : Set ℕ) (L : ℕ) : countBelow S L ≤ countUpTo S L + 1 := by
  unfold countBelow countUpTo
  have hsub : (range L).filter (· ∈ S) ⊆ insert 0 ((Icc 1 L).filter (· ∈ S)) := by
    intro n hn
    simp only [mem_filter, mem_range] at hn
    rcases Nat.eq_zero_or_pos n with h | h
    · exact h ▸ mem_insert_self _ _
    · exact mem_insert_of_mem (mem_filter.2 ⟨mem_Icc.2 ⟨h, by omega⟩, hn.2⟩)
  exact (card_le_card hsub).trans (card_insert_le _ _)

lemma countUpTo_mono (S : Set ℕ) {M N : ℕ} (h : M ≤ N) : countUpTo S M ≤ countUpTo S N := by
  apply card_le_card
  intro n hn
  simp only [mem_filter, mem_Icc] at hn ⊢
  exact ⟨⟨hn.1.1, by omega⟩, hn.2⟩

lemma countUpTo_le (S : Set ℕ) (N : ℕ) : countUpTo S N ≤ N :=
  (card_filter_le _ _).trans (by simp)

/-- **Key counting estimate.** For infinite `A` and `r ≥ 1` there are constants `K, c, N₁` with
`|{n < N : n is a sum of at most r elements of A}| ≤ K · |r^A ∩ [1, 2^r N + c]| + K`
for all `N ≥ N₁`. -/
lemma count_sumsAtMost_le {A : Set ℕ} {r : ℕ} (hinf : A.Infinite) (hr : 1 ≤ r) :
    ∃ K c N₁ : ℕ, 0 < K ∧ ∀ N ≥ N₁,
      countBelow (sumsAtMost r A) N ≤ K * countUpTo (distinctSums r A) (2 ^ r * N + c) + K := by
  -- a fixed set `T ⊆ A` of `r` elements, all below `c`
  obtain ⟨T, hTA, hTc⟩ := hinf.exists_subset_card_eq r
  obtain ⟨c, hc⟩ : ∃ c, ∀ t ∈ insert 0 T, t < c :=
    ⟨(insert 0 T).sup id + 1, fun t ht => Nat.lt_succ_of_le (le_sup (f := id) ht)⟩
  -- `A ∪ {0}` has at least `r + 1` elements below `N₂`
  obtain ⟨T', hT'A, hT'c⟩ := hinf.exists_subset_card_eq (r + 1)
  set N2 := T'.sup id + 1
  have hX : ∀ N ≥ N2, r + 1 ≤ countBelow (insert 0 A) N := by
    intro N hN
    rw [← hT'c]
    apply card_le_card
    intro t ht
    have := le_sup (f := id) ht
    simp only [mem_filter, mem_range]
    exact ⟨by simp at this; omega, Set.mem_insert_of_mem _ (hT'A ht)⟩
  set C := (1 + r * (r + 1)) ^ r
  refine ⟨C * (r + 1), c, N2, by positivity, ?_⟩
  intro N hN
  have h1 : countBelow (sumsAtMost r A) N ≤ isoCount (insert 0 A) r ∅ N := by
    apply card_le_card
    intro n hn
    obtain ⟨hnN, m, hcard, hmA, rfl⟩ := mem_filter.1 hn
    exact mem_filter.2 ⟨hnN, isoRep_empty_of_multiset A r m hcard hmA⟩
  have h2 := isoCount_le_distinct (insert 0 A) r N (hX N hN)
  have h3 := countBelow_shift (distinctSums r (insert 0 A)) (distinctSums r A) (insert 0 T) c
    (2 ^ r * N) hc (distinct_shift A r hr T hTA hTc)
  have h4 : (insert 0 T).card ≤ r + 1 := (card_insert_le _ _).trans (by rw [hTc])
  have h5 := countBelow_le_countUpTo (distinctSums r A) (2 ^ r * N + c)
  set x := countUpTo (distinctSums r A) (2 ^ r * N + c)
  have h6 : isoCount (insert 0 A) r ∅ N ≤ C * ((r + 1) * (x + 1)) :=
    h2.trans (Nat.mul_le_mul_left _ (h3.trans (Nat.mul_le_mul h4 h5)))
  have h7 : C * ((r + 1) * (x + 1)) = C * (r + 1) * x + C * (r + 1) := by ring
  omega

/-- **Quantitative form.** If `A` is a basis of order `r`, there are constants `K, c, N₀, N₁`
with `N ≤ K · |r^A ∩ [1, 2^r N + c]| + N₀` for all `N ≥ N₁`. -/
lemma main_bound {A : Set ℕ} {r : ℕ} (hA : IsAddBasisOfOrder A r) :
    ∃ K c N₀ N₁ : ℕ, 0 < K ∧ ∀ N ≥ N₁,
      N ≤ K * countUpTo (distinctSums r A) (2 ^ r * N + c) + N₀ := by
  obtain ⟨K, c, N1, hK, hcount⟩ := count_sumsAtMost_le (basis_infinite hA) (basis_order_pos hA)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hA
  refine ⟨K, c, K + N0, max N0 N1, hK, fun N hN => ?_⟩
  have h1 : N - N0 ≤ countBelow (sumsAtMost r A) N := by
    have hsub : Ico N0 N ⊆ (range N).filter (· ∈ sumsAtMost r A) := by
      intro n hn
      obtain ⟨h1, h2⟩ := mem_Ico.1 hn
      exact mem_filter.2 ⟨mem_range.2 h2, hN0 n h1⟩
    have hcard := card_le_card hsub
    rw [Nat.card_Ico] at hcard
    unfold countBelow
    exact hcard
  have h2 := hcount N (le_of_max_le_right hN)
  omega

/-! ### Erdős Problem 339 -/

/-- **Erdős Problem 339** (answer: yes; Hegyvári–Hennecart–Plagne 2003).
If `A ⊆ ℕ` is an additive basis of order `r` (every sufficiently large integer is a sum of at
most `r` elements of `A`), then the set of integers that are sums of exactly `r` pairwise
distinct elements of `A` has positive lower density. -/
theorem erdos_339 (A : Set ℕ) (r : ℕ) (hA : IsAddBasisOfOrder A r) :
    0 < lowerDensity (distinctSums r A) := by
  obtain ⟨K, c, N0, N1, hK, hmain⟩ := main_bound hA
  set D := distinctSums r A
  set D0 := 2 ^ r + c
  have hD0 : 0 < D0 := by positivity
  set δ : ℝ := 1 / (2 * D0 * K)
  have hδ : 0 < δ := by positivity
  have hev : ∀ᶠ L : ℕ in atTop, δ ≤ (countUpTo D L : ℝ) / L := by
    filter_upwards [eventually_ge_atTop (D0 * (N1 + 1) + 2 * D0 * (K + N0 + 1))] with L hL
    set N := L / D0
    have hN1 : N1 + 1 ≤ N := (Nat.le_div_iff_mul_le hD0).2 (by nlinarith)
    have hNL : D0 * N ≤ L := Nat.mul_div_le L D0
    have hLN : L < D0 * (N + 1) := Nat.lt_mul_div_succ L hD0
    have hle : 2 ^ r * N + c ≤ L := by
      have : 2 ^ r * N + c ≤ D0 * N := by
        simp only [D0, add_mul]; nlinarith
      omega
    set x := countUpTo D L
    have hx : N ≤ K * x + N0 := by
      have h1 := hmain N (by omega)
      have h2 : K * countUpTo D (2 ^ r * N + c) ≤ K * x :=
        Nat.mul_le_mul_left K (countUpTo_mono D hle)
      omega
    have hkey : L ≤ 2 * D0 * K * x := by nlinarith
    have hLpos : (0 : ℝ) < L := by
      have : 0 < L := by nlinarith
      exact_mod_cast this
    rw [div_le_div_iff₀ (by positivity) hLpos, one_mul]
    have : (L : ℝ) ≤ 2 * D0 * K * x := by exact_mod_cast hkey
    linarith
  have hcob : IsCoboundedUnder (· ≥ ·) atTop (fun N : ℕ => (countUpTo D N : ℝ) / N) := by
    refine isCoboundedUnder_ge_of_le atTop (x := 1) fun N => ?_
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h]
    · rw [div_le_one (by exact_mod_cast h)]
      exact_mod_cast countUpTo_le D N
  exact hδ.trans_le (le_liminf_of_le hcob hev)

end Erdos339


/-!
# Erdős Problem 339 — variants

* `erdos_339_exact`: the same conclusion when "basis of order `r`" is read as
  "every sufficiently large integer lies in the `r`-fold sumset `r • A`" (exactly `r` summands,
  repetitions allowed). This hypothesis implies the one used in `erdos_339`.
* `erdos_339_upper`: the companion question of Erdős and Graham — if the set of sums of (at most)
  `r` elements of `A` has positive upper density, so does the set of sums of exactly `r` distinct
  elements. `erdos_339_upper_exact` is the version with the `r`-fold sumset `r • A`.
-/


namespace Erdos339

open Finset Filter

open scoped Pointwise

open Classical

/-! ### Relating the two readings of "sum of `r` elements" -/

lemma nsmul_subset_sumsAtMost (A : Set ℕ) (r : ℕ) : r • A ⊆ sumsAtMost r A := by
  intro n h
  induction r generalizing n with
  | zero =>
    rw [zero_nsmul, Set.mem_zero] at h
    exact ⟨0, by simp, by simp, by simp [h]⟩
  | succ r ih =>
    rw [succ_nsmul, Set.mem_add] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    obtain ⟨m, hm, hmA, rfl⟩ := ih hx
    refine ⟨y ::ₘ m, by simp; omega, ?_, by simp [add_comm]⟩
    intro a ha
    rcases Multiset.mem_cons.1 ha with rfl | ha
    · exact hy
    · exact hmA a ha

/-- **Erdős Problem 339, exact-order reading.** If every sufficiently large integer is a sum of
exactly `r` elements of `A` (repetitions allowed), then the sums of exactly `r` distinct elements
of `A` have positive lower density. -/
theorem erdos_339_exact (A : Set ℕ) (r : ℕ) (hA : ∀ᶠ n in atTop, n ∈ r • A) :
    0 < lowerDensity (distinctSums r A) :=
  erdos_339 A r (hA.mono fun _ hn => nsmul_subset_sumsAtMost A r hn)

/-! ### Upper density -/

lemma density_seq_nonneg (S : Set ℕ) (N : ℕ) : 0 ≤ (countUpTo S N : ℝ) / N := by positivity

lemma density_seq_le_one (S : Set ℕ) (N : ℕ) : (countUpTo S N : ℝ) / N ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast countUpTo_le S N

lemma upperDensity_mono {S T : Set ℕ} (h : S ⊆ T) : upperDensity S ≤ upperDensity T := by
  apply limsup_le_limsup
  · exact Eventually.of_forall fun N => by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
      exact_mod_cast card_le_card fun n hn => by
        simp only [mem_filter] at hn ⊢
        exact ⟨hn.1, h hn.2⟩
  · exact isCoboundedUnder_le_of_le atTop (density_seq_nonneg S)
  · exact isBoundedUnder_of ⟨1, density_seq_le_one T⟩

/-- A bounded set has upper density `0` (in particular, not positive). -/
lemma not_pos_upperDensity_of_bdd (S : Set ℕ) (B : ℕ) (hS : ∀ n ∈ S, n ≤ B) :
    ¬ 0 < upperDensity S := by
  intro h
  have hfreq : ∃ᶠ N in atTop, upperDensity S / 2 < (countUpTo S N : ℝ) / N :=
    frequently_lt_of_lt_limsup (isCoboundedUnder_le_of_le atTop (density_seq_nonneg S))
      (by change upperDensity S / 2 < upperDensity S; linarith)
  have hev : ∀ᶠ N : ℕ in atTop, (countUpTo S N : ℝ) / N ≤ upperDensity S / 2 := by
    filter_upwards [eventually_ge_atTop (⌈2 * B / upperDensity S⌉₊ + 1)] with N hN
    have hcount : countUpTo S N ≤ B := by
      refine (card_le_card (s := (Icc 1 N).filter (· ∈ S)) (t := Icc 1 B) ?_).trans (by simp)
      intro n hn
      simp only [mem_filter, mem_Icc] at hn ⊢
      exact ⟨hn.1.1, hS n hn.2⟩
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hN' : 2 * B / upperDensity S < N := by
      have := Nat.le_ceil (2 * B / upperDensity S)
      have h2 : ((⌈2 * B / upperDensity S⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
      push_cast at h2
      linarith
    rw [div_lt_iff₀ h] at hN'
    rw [div_le_iff₀ hNpos]
    have : (countUpTo S N : ℝ) ≤ B := by exact_mod_cast hcount
    nlinarith
  obtain ⟨N, h1, h2⟩ := (hfreq.and_eventually hev).exists
  linarith

/-- **Companion question of Erdős and Graham** (answer: yes; Hegyvári–Hennecart–Plagne 2003).
If the set of integers that are sums of at most `r` elements of `A` has positive upper density,
then the set of sums of exactly `r` pairwise distinct elements of `A` has positive upper
density. -/
theorem erdos_339_upper (A : Set ℕ) (r : ℕ) (h : 0 < upperDensity (sumsAtMost r A)) :
    0 < upperDensity (distinctSums r A) := by
  by_cases hr : r = 0
  · subst hr
    refine absurd h (not_pos_upperDensity_of_bdd _ 0 ?_)
    rintro n ⟨m, hc, -, rfl⟩
    obtain rfl : m = 0 := Multiset.card_eq_zero.1 (Nat.le_zero.1 hc)
    simp
  by_cases hfin : A.Finite
  · obtain ⟨M, hM⟩ := hfin.bddAbove
    refine absurd h (not_pos_upperDensity_of_bdd _ (r * M) ?_)
    rintro n ⟨m, hc, hmA, rfl⟩
    have h1 := Multiset.sum_le_card_nsmul m M (fun x hx => hM (hmA x hx))
    rw [smul_eq_mul] at h1
    exact h1.trans (Nat.mul_le_mul_right M hc)
  obtain ⟨K, c, N1, hK, hcount⟩ := count_sumsAtMost_le (r := r) hfin (by omega)
  set S := sumsAtMost r A
  set D := distinctSums r A
  set δ : ℝ := upperDensity S / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hfreq : ∃ᶠ N in atTop, δ < (countUpTo S N : ℝ) / N :=
    frequently_lt_of_lt_limsup (isCoboundedUnder_le_of_le atTop (density_seq_nonneg S))
      (by change δ < upperDensity S; linarith)
  set D0 := 2 ^ r + c
  have hD0 : 0 < D0 := by positivity
  set δ' : ℝ := δ / (4 * K * D0)
  have hδ' : 0 < δ' := by positivity
  have hfreq' : ∃ᶠ M in atTop, δ' ≤ (countUpTo D M : ℝ) / M := by
    rw [frequently_atTop] at hfreq ⊢
    intro a
    obtain ⟨N, hN, hδN⟩ := hfreq (max a (max N1 (⌈2 * K / δ⌉₊ + 1)))
    have haN : a ≤ N := le_of_max_le_left hN
    have hN1 : N1 ≤ N := le_of_max_le_left (le_of_max_le_right hN)
    have hNbig : ⌈2 * K / δ⌉₊ + 1 ≤ N := le_of_max_le_right (le_of_max_le_right hN)
    refine ⟨D0 * (N + 1), ?_, ?_⟩
    · nlinarith
    set x := countUpTo D (D0 * (N + 1))
    -- `|S ∩ [1, N]| ≤ K x + K`
    have hsN : countUpTo S N ≤ K * x + K := by
      have h1 : countUpTo S N ≤ countBelow S (N + 1) := by
        apply card_le_card
        intro n hn
        simp only [mem_filter, mem_Icc, mem_range] at hn ⊢
        exact ⟨by omega, hn.2⟩
      have h2 := hcount (N + 1) (by omega)
      have h3 : K * countUpTo D (2 ^ r * (N + 1) + c) ≤ K * x := by
        apply Nat.mul_le_mul_left
        apply countUpTo_mono
        simp only [D0, add_mul]
        nlinarith
      omega
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
    have hD0pos : (0 : ℝ) < D0 := by exact_mod_cast hD0
    have hδN' : δ * N < K * x + K := by
      rw [lt_div_iff₀ hNpos] at hδN
      have : (countUpTo S N : ℝ) ≤ K * x + K := by exact_mod_cast hsN
      linarith
    have hKN : 2 * K ≤ δ * N := by
      have h1 := Nat.le_ceil (2 * K / δ)
      have h2 : ((⌈2 * K / δ⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hNbig
      push_cast at h2
      have h3 : 2 * (K : ℝ) / δ ≤ N := by linarith
      rw [div_le_iff₀ hδ] at h3
      linarith
    have hMpos : (0 : ℝ) < ((D0 * (N + 1) : ℕ) : ℝ) := by positivity
    rw [div_le_div_iff₀ (by positivity) hMpos]
    push_cast
    have hx : δ * N < 2 * K * x := by nlinarith
    have hN1' : (N : ℝ) + 1 ≤ 2 * N := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hN1' (le_of_lt (mul_pos hδ hD0pos))]
  exact hδ'.trans_le (le_limsup_of_frequently_le hfreq' (isBoundedUnder_of ⟨1, density_seq_le_one D⟩))

/-- **Companion question, exact-order reading.** If the `r`-fold sumset `r • A` has positive
upper density, then the sums of exactly `r` distinct elements of `A` have positive upper
density. -/
theorem erdos_339_upper_exact (A : Set ℕ) (r : ℕ) (h : 0 < upperDensity (r • A)) :
    0 < upperDensity (distinctSums r A) :=
  erdos_339_upper A r (h.trans_le (upperDensity_mono (nsmul_subset_sumsAtMost A r)))

end Erdos339


/-!
# Sanity checks on the definitions (non-vacuity, distinctness is enforced)
-/

namespace Erdos339

open Filter

/-- `ℕ` itself is an additive basis of order `1`, so the hypothesis of `erdos_339` is
satisfiable. -/
example : IsAddBasisOfOrder Set.univ 1 :=
  Eventually.of_forall fun n => ⟨{n}, by simp, by simp, by simp⟩

/-- Repetitions are not allowed in `distinctSums`: `2 = 1 + 1` is not a sum of two distinct
elements of `{1}`. -/
example : 2 ∉ distinctSums 2 {1} := by
  rintro ⟨S, hS, hSA, -⟩
  have : S ⊆ {1} := fun x hx => by simpa using hSA hx
  have := Finset.card_le_card this
  simp at this
  omega

/-- `5 = 2 + 3` is a sum of two distinct elements of `{1, 2, 3}`. -/
example : 5 ∈ distinctSums 2 {1, 2, 3} :=
  ⟨{2, 3}, by decide, by intro x; simp; omega, by decide⟩

/-- Repetitions are allowed in `sumsAtMost`: `2 = 1 + 1`. -/
example : 2 ∈ sumsAtMost 2 {1} := ⟨{1, 1}, by simp, by simp, by simp⟩

end Erdos339
