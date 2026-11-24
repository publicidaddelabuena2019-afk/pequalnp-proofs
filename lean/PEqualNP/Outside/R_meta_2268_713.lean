import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2268_713
    (padding : ∀ (n : ℕ) (A : Finset (Fin n)) (h : (Fin n → Bool) → Bool),
      (∀ i ∈ A, ∀ (x : Fin n → Bool) (b : Bool), h (Function.update x i b) = h x) →
      (∀ t, PEqualNP.MetaComplexity.HasCircuitSize n h t → PEqualNP.MetaComplexity.HasCircuitSize n (fun x => decide (∃ i ∈ A, x i = true) || h x) (t + A.card)) ∧
      ((∃ x, h x = false) → (∃ x, h x = true) → ∀ s,
        PEqualNP.MetaComplexity.HasCircuitSize n (fun x => decide (∃ i ∈ A, x i = true) || h x) s →
        ∃ t, t + A.card ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize n h t))
    (stars : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (e : (Fin n → Bool) → Bool),
      3 ≤ S.card → (∀ i ∈ S, (G.neighborSet i).ncard = 3) →
      (∀ i j, G.Adj i j → i ∈ S ∨ j ∈ S) → (∀ i ∈ S, ∀ j ∈ S, ¬G.Adj i j) →
      (∀ x, e x = true ↔ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) →
      ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ ∃ t, t + 9 ≤ 4 * S.card ∧
        PEqualNP.MetaComplexity.HasCircuitSize n (fun x => e (Function.update (Function.update x u false) v false)) t)
    (small : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (e : (Fin n → Bool) → Bool),
      (∀ i, (∃ j, G.Adj i j) → (G.neighborSet i).ncard = 3) →
      (∀ i (w : G.Walk i i), w.IsCycle → 7 ≤ w.length) →
      3 ≤ S.card → (∀ i ∈ S, ∃ j, G.Adj i j) →
      (∀ i j, G.Adj i j → i ∈ S ∨ j ∈ S) → (∀ i ∈ S, ∀ j ∈ S, ¬G.Adj i j) →
      (∀ x, e x = true ↔ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) →
      ∀ s, s + 1 < 4 * S.card → PEqualNP.MetaComplexity.HasCircuitSize n e s → (∀ r, PEqualNP.MetaComplexity.HasCircuitSize n e r → s ≤ r) →
      ∃ u v, (∃ j, G.Adj u j) ∧ (∃ j, G.Adj v j) ∧ u ≠ v ∧ ¬G.Adj u v ∧
        ∃ t, t + 8 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x => e (Function.update (Function.update x u false) v false)) t) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), x2.Colorable (2 : ℕ) → (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ∀ (x11 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x11 → ∃ (x13 : Fin x1) (x14 : Fin x1), x13 ∉ x3 ∧ x14 ∉ x3 ∧ x13 ≠ x14 ∧ ¬x2.Adj x13 x14 ∧ ∃ (x15 : ℕ), x15 + (8 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => x4 (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false)) x15 := by
  classical
  intro n G A f bip deg girth iso edge eval s hs
  obtain ⟨c⟩ := bip
  obtain ⟨p,q,hpq⟩ := edge
  let S := Finset.univ.filter fun i => c i ≠ c p ∧ ∃ j, G.Adj i j
  have mem (i : Fin n) : i ∈ S ↔ c i ≠ c p ∧ ∃ j, G.Adj i j := by simp [S]
  have pos (i : Fin n) (hi : i ∈ S) := ((mem i).mp hi).2
  have active (i : Fin n) (hi : ∃ j, G.Adj i j) : i ∉ A := by
    obtain ⟨j,hj⟩ := hi
    exact iso i j hj
  have dg (i : Fin n) (hi : ∃ j, G.Adj i j) := deg i (active i hi)
  have sizeS : 3 ≤ S.card := by
    have sub : G.neighborFinset p ⊆ S := by
      intro i hi
      have hpi := (G.mem_neighborFinset p i).mp hi
      exact (mem i).mpr ⟨(c.valid hpi).symm, p, hpi.symm⟩
    have hc := Finset.card_le_card sub
    have hdeg := dg p ⟨q,hpq⟩
    simp only [SimpleGraph.ncard_neighborSet, SimpleGraph.card_neighborFinset_eq_degree] at hdeg hc
    omega
  have cover (i j : Fin n) (hij : G.Adj i j) : i ∈ S ∨ j ∈ S := by
    by_cases h : c i = c p
    · exact Or.inr ((mem j).2 ⟨fun e => c.valid hij (h.trans e.symm),i,hij.symm⟩)
    · exact Or.inl ((mem i).2 ⟨h,j,hij⟩)
  have indep (i : Fin n) (hi : i ∈ S) (j : Fin n) (hj : j ∈ S) : ¬G.Adj i j := by
    intro he
    have f1 := ((mem i).1 hi).1
    have f2 := ((mem j).1 hj).1
    have hi' : (c i).val ≠ (c p).val := fun e => f1 (Fin.ext e)
    have hj' : (c j).val ≠ (c p).val := fun e => f2 (Fin.ext e)
    exact c.valid he (Fin.ext (by have := (c i).isLt; have := (c j).isLt; have := (c p).isLt; omega))
  let e (x : Fin n → Bool) := decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)
  have ee (x) : e x = true ↔ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true := by simp [e]
  have free (a : Fin n) (ha : a ∈ A) (x : Fin n → Bool) (b : Bool) :
      e (Function.update x a b) = e x := by
    apply Bool.eq_iff_iff.mpr
    rw [ee, ee]
    constructor <;> rintro ⟨i,j,hij,hi,hj⟩ <;>
      have hia : i ≠ a := fun eq => iso i j hij (eq ▸ ha) <;>
      have hja : j ≠ a := fun eq => iso j i hij.symm (eq ▸ ha)
    · exact ⟨i,j,hij,by simpa [Function.update_of_ne hia] using hi,
        by simpa [Function.update_of_ne hja] using hj⟩
    · exact ⟨i,j,hij,by simpa [Function.update_of_ne hia] using hi,
        by simpa [Function.update_of_ne hja] using hj⟩
  have fEq (x : Fin n → Bool) : f x = (decide (∃ a ∈ A, x a = true) || e x) := by
    apply Bool.eq_iff_iff.mpr
    simp only [eval, Bool.or_eq_true, decide_eq_true_iff, ee]
  have zero : ∃ x, e x = false := ⟨fun _ => false, by simp [e]⟩
  have one : ∃ x, e x = true := ⟨fun _ => true, (ee _).2 ⟨p,q,hpq,rfl,rfl⟩⟩
  rw [funext fEq] at hs
  obtain ⟨k,hk,hek⟩ := (padding n A e free).2 zero one s hs
  obtain ⟨u,v,hu,hv,huv,hn,t,ht,het⟩ :
      ∃ u v, (∃ j, G.Adj u j) ∧ (∃ j, G.Adj v j) ∧ u ≠ v ∧ ¬G.Adj u v ∧
        ∃ t, t + 8 ≤ k ∧ PEqualNP.MetaComplexity.HasCircuitSize n
          (fun x => e (Function.update (Function.update x u false) v false)) t := by
    by_cases h : k + 1 < 4*S.card
    · have existsSize : ∃ r, PEqualNP.MetaComplexity.HasCircuitSize n e r := ⟨k,hek⟩
      have hkmin := Nat.find_min' existsSize hek
      obtain ⟨u,v,hu,hv,huv,hn,t,ht,he⟩ := small n G S e dg girth sizeS pos cover indep ee
        (Nat.find existsSize) (by omega) (Nat.find_spec existsSize)
        (fun r hr => Nat.find_min' existsSize hr)
      exact ⟨u,v,hu,hv,huv,hn,t,by omega,he⟩
    · obtain ⟨u,hu,v,hv,huv,t,ht,he⟩ := stars n G S e sizeS
        (fun i hi => dg i (pos i hi)) cover indep ee
      exact ⟨u,v,pos u hu,pos v hv,huv,indep u hu v hv,t,by omega,he⟩
  have hua := active u hu
  have hva := active v hv
  let d (x : Fin n → Bool) := Function.update (Function.update x u false) v false
  have compat (a : Fin n) (ha : a ∈ A) (x : Fin n → Bool) (b : Bool) :
      d (Function.update x a b) = Function.update (d x) a b := by
    have hau : a ≠ u := fun eq => hua (eq ▸ ha)
    have hav : a ≠ v := fun eq => hva (eq ▸ ha)
    funext i
    by_cases iv : i = v <;> by_cases iu : i = u <;> by_cases ia : i = a <;>
      simp_all only [d, Function.update_apply, ↓reduceIte]
  have ec (a : Fin n) (ha : a ∈ A) (x : Fin n → Bool) (b : Bool) :
      e (d (Function.update x a b)) = e (d x) := by rw [compat a ha, free a ha]
  have lift := (padding n A (fun x => e (d x)) ec).1 t het
  refine ⟨u,v,hua,hva,huv,hn,t + A.card,by omega,?_⟩
  have final (x : Fin n → Bool) : f (d x) = (decide (∃ a ∈ A, x a = true) || e (d x)) := by
    rw [fEq]
    have heq (a : Fin n) (ha : a ∈ A) : d x a = x a := by
      have hau : a ≠ u := fun eq => hua (eq ▸ ha)
      have hav : a ≠ v := fun eq => hva (eq ▸ ha)
      simp [d, Function.update_of_ne hav, Function.update_of_ne hau]
    have same : (∃ a ∈ A, d x a = true) ↔ ∃ a ∈ A, x a = true := by
      constructor <;> rintro ⟨a,ha,hx⟩ <;> exact ⟨a,ha,by simpa only [heq a ha] using hx⟩
    simp only [same]
  change PEqualNP.MetaComplexity.HasCircuitSize n (fun x => f (d x)) _
  rw [funext final]
  exact lift
