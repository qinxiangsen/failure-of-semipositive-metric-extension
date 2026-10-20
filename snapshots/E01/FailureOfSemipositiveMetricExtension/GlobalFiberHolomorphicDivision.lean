import FailureOfSemipositiveMetricExtension.GlobalFiberSectionDivision

/-! Actual complex C-infinity line-bundle sections, local gluing, and division.
This is the regularity used by the holomorphic structure sheaf, with no
unproved multivariable upgrade to analytic regularity. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.Holomorphic
noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff Topology

structure SectionData (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) where
  coefficient : Index → Fiber t → ℂ
  analytic : ∀ i, ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ∞ (coefficient i) (baseSet t i)
  compatible : ∀ i j p, p ∈ baseSet t i ∩ baseSet t j →
    gain t a b i j p * coefficient i p = coefficient j p

def sectionValue {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData t a b) (p : Fiber t) :
    (core t a b).Fiber p := s.coefficient ((core t a b).indexAt p) p

def sectionMap {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData t a b) :
    Fiber t → (core t a b).TotalSpace := fun p => ⟨p,sectionValue s p⟩

@[simp] theorem sectionMap_projects {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ}
    (s : SectionData t a b) (p : Fiber t) : (core t a b).proj (sectionMap s p) = p := rfl

theorem sectionMap_localTriv {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData t a b)
    (i : Index) (p : Fiber t) (hp : p ∈ baseSet t i) :
    (core t a b).localTriv i (sectionMap s p) = (p,s.coefficient i p) := by
  rw [VectorBundleCore.localTriv_apply]
  congr 1
  exact s.compatible ((core t a b).indexAt p) i p ⟨(core t a b).mem_baseSet_at p,hp⟩

theorem sectionMap_contMDiff {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData t a b) :
    ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ∞ (sectionMap s) := by
  intro p
  let i := (core t a b).indexAt p
  have hp : p ∈ baseSet t i := (core t a b).mem_baseSet_at p
  let e := (core t a b).localTriv i
  haveI : MemTrivializationAtlas e := ⟨⟨i,rfl⟩⟩
  apply (e.contMDiffAt_iff (show sectionMap s p ∈ e.source from hp)).mpr
  refine ⟨contMDiffAt_id,?_⟩
  have hnb : baseSet t i ∈ 𝓝 p := (core t a b).isOpen_baseSet i |>.mem_nhds hp
  exact ((s.analytic i).congr (fun q hq =>
    congrArg Prod.snd (sectionMap_localTriv s i q hq))).contMDiffAt hnb

theorem sectionValue_zero_iff {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData t a b)
    (i : Index) (p : Fiber t) (hp : p ∈ baseSet t i) :
    sectionValue s p = 0 ↔ s.coefficient i p = 0 := by
  have hc := s.compatible ((core t a b).indexAt p) i p ⟨(core t a b).mem_baseSet_at p,hp⟩
  have hi := s.compatible i ((core t a b).indexAt p) p ⟨hp,(core t a b).mem_baseSet_at p⟩
  constructor
  · intro hz
    change s.coefficient ((core t a b).indexAt p) p = 0 at hz
    simpa [hz] using hc.symm
  · intro hz
    change s.coefficient ((core t a b).indexAt p) p = 0
    simpa [hz] using hi.symm


/-- Forget only the stronger regularity, preserving every actual coefficient. -/
def ofAnalyticData {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ}
    (s : FixedFiberBundle.SectionData t a b) : SectionData t a b where
  coefficient := s.coefficient
  analytic i := (s.analytic i).of_le le_top
  compatible := s.compatible

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.Holomorphic

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.Holomorphic
noncomputable section
open Set Bundle IsManifold FailureOfSemipositiveMetricExtension.GlobalIncidence
open scoped Manifold ContDiff Topology

structure LocalSectionData (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) (U : Set (Fiber t)) where
  coefficient : Index → Fiber t → ℂ
  analytic : ∀ i, ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ∞ (coefficient i) (U ∩ baseSet t i)
  compatible : ∀ i j p, p ∈ U → p ∈ baseSet t i ∩ baseSet t j →
    gain t a b i j p * coefficient i p = coefficient j p

/-- A scalar analytic function in one actual trivialization defines a local bundle section. -/
def localSectionOfTrivialization (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) (U : Set (Fiber t)) (j : Index)
    (hU : U ⊆ baseSet t j) (f : Fiber t → ℂ)
    (hf : ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ∞ f U) : LocalSectionData t a b U where
  coefficient i p := gain t a b j i p * f p
  analytic i := by
    have hg := (gain_contMDiffOn t a b j i ∞).mono
      (show U ∩ baseSet t i ⊆ baseSet t j ∩ baseSet t i from fun _ hp => ⟨hU hp.1,hp.2⟩)
    exact hg.smul (hf.mono inter_subset_left)
  compatible i k p hp hik := by
    rw [← mul_assoc,gain_comp t a b j i k p ⟨⟨hU hp,hik.1⟩,hik.2⟩]

/-- Gluing analytic local sections requires equality on every actual overlap.
No geometric existence statement is assumed here. -/
def glueSections {K : Type*} (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) (U : K → Set (Fiber t))
    (hopen : ∀ k, IsOpen (U k)) (hcover : ∀ p, ∃ k, p ∈ U k)
    (s : ∀ k, LocalSectionData t a b (U k))
    (hcompat : ∀ k l i p, p ∈ U k → p ∈ U l → p ∈ baseSet t i →
      (s k).coefficient i p = (s l).coefficient i p) : SectionData t a b where
  coefficient i p := (s (Classical.choose (hcover p))).coefficient i p
  analytic i := by
    intro p hp
    let k := Classical.choose (hcover p)
    have hpk : p ∈ U k := Classical.choose_spec (hcover p)
    have hnb : U k ∩ baseSet t i ∈ 𝓝 p :=
      ((hopen k).inter (baseSet_isOpen t i)).mem_nhds ⟨hpk,hp⟩
    have ha := ((s k).analytic i).contMDiffAt hnb
    apply ContMDiffAt.contMDiffWithinAt
    apply ha.congr_of_eventuallyEq
    filter_upwards [hnb] with q hq
    exact hcompat (Classical.choose (hcover q)) k i q
      (Classical.choose_spec (hcover q)) hq.1 hq.2
  compatible i j p hp := (s (Classical.choose (hcover p))).compatible i j p
    (Classical.choose_spec (hcover p)) hp

theorem glueSections_coefficient {K : Type*} (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) (U : K → Set (Fiber t))
    (hopen : ∀ k, IsOpen (U k)) (hcover : ∀ p, ∃ k, p ∈ U k)
    (s : ∀ k, LocalSectionData t a b (U k))
    (hcompat : ∀ k l i p, p ∈ U k → p ∈ U l → p ∈ baseSet t i →
      (s k).coefficient i p = (s l).coefficient i p)
    (k : K) (i : Index) (p : Fiber t) (hp : p ∈ U k) (hi : p ∈ baseSet t i) :
    (glueSections t a b U hopen hcover s hcompat).coefficient i p = (s k).coefficient i p :=
  hcompat _ k i p (Classical.choose_spec (hcover p)) hp hi
end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.Holomorphic

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.Holomorphic
noncomputable section
open Set Bundle IsManifold FailureOfSemipositiveMetricExtension.GlobalIncidence
open scoped Manifold ContDiff

theorem localDivision_identity {t : ℂ} {a c : ℤ} {b d : Fin 4 → ℤ}
    (D : SectionData t c d) (N : SectionData t (a+c) (fun r => b r+d r))
    (U : Set (Fiber t)) (j : Index) (hU : U ⊆ baseSet t j) (f : Fiber t → ℂ)
    (hf : ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ∞ f U)
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
    (hf : ∀ k, ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ∞ (f k) (U k))
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
    (hf : ∀ k, ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ∞ (f k) (U k))
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
    (hf : ∀ k, ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ∞ (f k) (U k))
    (hdiv : ∀ k p, p ∈ U k → f k p * D.coefficient (j k) p = N.coefficient (j k) p)
    (i : Index) (p : Fiber t) (hi : p ∈ baseSet t i) :
    (divideSections D N Z hZ hD U hopen hcover j hU f hf hdiv).coefficient i p *
      D.coefficient i p = N.coefficient i p := by
  obtain ⟨k,hk⟩ := hcover p
  rw [divideSections_coefficient D N Z hZ hD U hopen hcover j hU f hf hdiv k i p hk hi]
  exact localDivision_identity D N (U k) (j k) (hU k) (f k) (hf k) (hdiv k) i p hk hi

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.Holomorphic
