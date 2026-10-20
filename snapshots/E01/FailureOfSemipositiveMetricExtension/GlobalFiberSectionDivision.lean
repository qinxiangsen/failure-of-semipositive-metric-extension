import FailureOfSemipositiveMetricExtension.GlobalFiberSectionGluing
import FailureOfSemipositiveMetricExtension.GlobalFiberSectionProducts

/-! Actual fixed-fibre analytic section division from regular local quotients.
The density, nonvanishing, cover, and local quotient premises are explicit.
No geometric existence or regularity premise is silently assumed. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold FailureOfSemipositiveMetricExtension.GlobalIncidence
open scoped Manifold ContDiff

theorem localDivision_identity {t : ℂ} {a c : ℤ} {b d : Fin 4 → ℤ}
    (D : SectionData t c d) (N : SectionData t (a+c) (fun r => b r+d r))
    (U : Set (Fiber t)) (j : Index) (hU : U ⊆ baseSet t j) (f : Fiber t → ℂ)
    (hf : ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω f U)
    (hdiv : ∀ p ∈ U, f p * D.coefficient j p = N.coefficient j p)
    (i : Index) (p : Fiber t) (hp : p ∈ U) (hi : p ∈ baseSet t i) :
    (localSectionOfTrivialization t a b U j hU f hf).coefficient i p * D.coefficient i p =
      N.coefficient i p := by
  have hj := hU hp
  have hD := D.compatible j i p ⟨hj,hi⟩
  have hN := N.compatible j i p ⟨hj,hi⟩
  change (gain t a b j i p * f p) * D.coefficient i p = _
  rw [← hD]
  calc
    (gain t a b j i p * f p) * (gain t c d j i p * D.coefficient j p) =
        (gain t a b j i p * gain t c d j i p) * (f p * D.coefficient j p) := by ring
    _ = gain t (a+c) (fun r => b r+d r) j i p * N.coefficient j p := by
      rw [← gain_add t a c b d j i p ⟨hj,hi⟩,hdiv p hp]
    _ = N.coefficient i p := hN

theorem localDivision_compatible {t : ℂ} {a c : ℤ} {b d : Fin 4 → ℤ}
    (D : SectionData t c d) (N : SectionData t (a+c) (fun r => b r+d r))
    (Z : Set (Fiber t)) (hZ : Dense Z)
    (hD : ∀ p ∈ Z, ∀ i, p ∈ baseSet t i → D.coefficient i p ≠ 0)
    (U V : Set (Fiber t)) (hU : IsOpen U) (hV : IsOpen V)
    (s : LocalSectionData t a b U) (v : LocalSectionData t a b V)
    (hs : ∀ i p, p ∈ U → p ∈ baseSet t i → s.coefficient i p * D.coefficient i p = N.coefficient i p)
    (ht : ∀ i p, p ∈ V → p ∈ baseSet t i → v.coefficient i p * D.coefficient i p = N.coefficient i p)
    (i : Index) (p : Fiber t) (hpU : p ∈ U) (hpV : p ∈ V) (hpi : p ∈ baseSet t i) :
    s.coefficient i p = v.coefficient i p := by
  let W := U ∩ V ∩ baseSet t i
  have hW : IsOpen W := (hU.inter hV).inter (baseSet_isOpen t i)
  have he : EqOn (s.coefficient i) (v.coefficient i) (W ∩ Z) := by
    intro q hq
    apply mul_right_cancel₀ (hD q hq.2 i hq.1.2)
    exact (hs i q hq.1.1.1 hq.1.2).trans (ht i q hq.1.1.2 hq.1.2).symm
  have hext := he.of_subset_closure
    (((s.analytic i).continuousOn).mono (show W ⊆ U ∩ baseSet t i from fun _ h => ⟨h.1.1,h.2⟩))
    (((v.analytic i).continuousOn).mono (show W ⊆ V ∩ baseSet t i from fun _ h => ⟨h.1.2,h.2⟩))
    inter_subset_left (hZ.open_subset_closure_inter hW)
  exact hext ⟨⟨hpU,hpV⟩,hpi⟩

/-- Verified regular local quotients glue to a genuine analytic quotient section. -/
def divideSections {K : Type*} {t : ℂ} {a c : ℤ} {b d : Fin 4 → ℤ}
    (D : SectionData t c d) (N : SectionData t (a+c) (fun r => b r+d r))
    (Z : Set (Fiber t)) (hZ : Dense Z)
    (hD : ∀ p ∈ Z, ∀ i, p ∈ baseSet t i → D.coefficient i p ≠ 0)
    (U : K → Set (Fiber t)) (hopen : ∀ k, IsOpen (U k)) (hcover : ∀ p, ∃ k, p ∈ U k)
    (j : K → Index) (hU : ∀ k, U k ⊆ baseSet t (j k))
    (f : K → Fiber t → ℂ)
    (hf : ∀ k, ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω (f k) (U k))
    (hdiv : ∀ k p, p ∈ U k → f k p * D.coefficient (j k) p = N.coefficient (j k) p) :
    SectionData t a b :=
  glueSections t a b U hopen hcover
    (fun k => localSectionOfTrivialization t a b (U k) (j k) (hU k) (f k) (hf k))
    (fun k l i p hk hl hi => localDivision_compatible D N Z hZ hD _ _ (hopen k) (hopen l)
      _ _ (fun i p hp hi => localDivision_identity D N _ _ (hU k) _ (hf k) (hdiv k) i p hp hi)
      (fun i p hp hi => localDivision_identity D N _ _ (hU l) _ (hf l) (hdiv l) i p hp hi)
      i p hk hl hi)

theorem divideSections_coefficient {K : Type*} {t : ℂ} {a c : ℤ} {b d : Fin 4 → ℤ}
    (D : SectionData t c d) (N : SectionData t (a+c) (fun r => b r+d r))
    (Z : Set (Fiber t)) (hZ : Dense Z)
    (hD : ∀ p ∈ Z, ∀ i, p ∈ baseSet t i → D.coefficient i p ≠ 0)
    (U : K → Set (Fiber t)) (hopen : ∀ k, IsOpen (U k)) (hcover : ∀ p, ∃ k, p ∈ U k)
    (j : K → Index) (hU : ∀ k, U k ⊆ baseSet t (j k))
    (f : K → Fiber t → ℂ)
    (hf : ∀ k, ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω (f k) (U k))
    (hdiv : ∀ k p, p ∈ U k → f k p * D.coefficient (j k) p = N.coefficient (j k) p)
    (k : K) (i : Index) (p : Fiber t) (hp : p ∈ U k) (hi : p ∈ baseSet t i) :
    (divideSections D N Z hZ hD U hopen hcover j hU f hf hdiv).coefficient i p =
      gain t a b (j k) i p * f k p := by
  unfold divideSections
  exact glueSections_coefficient _ _ _ _ _ _ _ _ k i p hp hi

/-- The genuine quotient satisfies the division equation in every actual frame. -/
theorem divideSections_mul_coefficient {K : Type*} {t : ℂ} {a c : ℤ} {b d : Fin 4 → ℤ}
    (D : SectionData t c d) (N : SectionData t (a+c) (fun r => b r+d r))
    (Z : Set (Fiber t)) (hZ : Dense Z)
    (hD : ∀ p ∈ Z, ∀ i, p ∈ baseSet t i → D.coefficient i p ≠ 0)
    (U : K → Set (Fiber t)) (hopen : ∀ k, IsOpen (U k)) (hcover : ∀ p, ∃ k, p ∈ U k)
    (j : K → Index) (hU : ∀ k, U k ⊆ baseSet t (j k))
    (f : K → Fiber t → ℂ)
    (hf : ∀ k, ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω (f k) (U k))
    (hdiv : ∀ k p, p ∈ U k → f k p * D.coefficient (j k) p = N.coefficient (j k) p)
    (i : Index) (p : Fiber t) (hi : p ∈ baseSet t i) :
    (divideSections D N Z hZ hD U hopen hcover j hU f hf hdiv).coefficient i p *
      D.coefficient i p = N.coefficient i p := by
  obtain ⟨k,hk⟩ := hcover p
  rw [divideSections_coefficient D N Z hZ hD U hopen hcover j hU f hf hdiv k i p hk hi]
  exact localDivision_identity D N (U k) (j k) (hU k) (f k) (hf k) (hdiv k) i p hk hi

/-- The section product recovers the numerator at every point of the actual fixed fibre. -/
theorem divideSections_mul_value {K : Type*} {t : ℂ} {a c : ℤ} {b d : Fin 4 → ℤ}
    (D : SectionData t c d) (N : SectionData t (a+c) (fun r => b r+d r))
    (Z : Set (Fiber t)) (hZ : Dense Z)
    (hD : ∀ p ∈ Z, ∀ i, p ∈ baseSet t i → D.coefficient i p ≠ 0)
    (U : K → Set (Fiber t)) (hopen : ∀ k, IsOpen (U k)) (hcover : ∀ p, ∃ k, p ∈ U k)
    (j : K → Index) (hU : ∀ k, U k ⊆ baseSet t (j k))
    (f : K → Fiber t → ℂ)
    (hf : ∀ k, ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω (f k) (U k))
    (hdiv : ∀ k p, p ∈ U k → f k p * D.coefficient (j k) p = N.coefficient (j k) p)
    (p : Fiber t) :
    sectionValue (multiplySections
      (divideSections D N Z hZ hD U hopen hcover j hU f hf hdiv) D) p = sectionValue N p :=
  divideSections_mul_coefficient D N Z hZ hD U hopen hcover j hU f hf hdiv
    ((core t (a+c) (fun r => b r+d r)).indexAt p) p
    ((core t (a+c) (fun r => b r+d r)).mem_baseSet_at p)

/-- The actual analytic section maps satisfy the global division identity. -/
theorem divideSections_mul_sectionMap {K : Type*} {t : ℂ} {a c : ℤ} {b d : Fin 4 → ℤ}
    (D : SectionData t c d) (N : SectionData t (a+c) (fun r => b r+d r))
    (Z : Set (Fiber t)) (hZ : Dense Z)
    (hD : ∀ p ∈ Z, ∀ i, p ∈ baseSet t i → D.coefficient i p ≠ 0)
    (U : K → Set (Fiber t)) (hopen : ∀ k, IsOpen (U k)) (hcover : ∀ p, ∃ k, p ∈ U k)
    (j : K → Index) (hU : ∀ k, U k ⊆ baseSet t (j k))
    (f : K → Fiber t → ℂ)
    (hf : ∀ k, ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω (f k) (U k))
    (hdiv : ∀ k p, p ∈ U k → f k p * D.coefficient (j k) p = N.coefficient (j k) p) :
    sectionMap (multiplySections
      (divideSections D N Z hZ hD U hopen hcover j hU f hf hdiv) D) = sectionMap N := by
  funext p
  exact congrArg (fun v => Bundle.TotalSpace.mk p v)
    (divideSections_mul_value D N Z hZ hD U hopen hcover j hU f hf hdiv p)

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
