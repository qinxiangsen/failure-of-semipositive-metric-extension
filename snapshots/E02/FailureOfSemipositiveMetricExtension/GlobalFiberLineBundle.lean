import FailureOfSemipositiveMetricExtension.GlobalFiberManifold
import FailureOfSemipositiveMetricExtension.GlobalAnalyticLineBundle

/-! Actual rank-one analytic line bundles on each fixed fibre, constructed by
pulling back the verified global transition cocycle along the analytic inclusion.
The canonical map of total spaces is fibrewise linear and respects trivializations. -/

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff

abbrev Index := FailureOfSemipositiveMetricExtension.GlobalLineBundle.Index

def baseSet (t : ℂ) (i : Index) : Set (Fiber t) :=
  FixedFiber.inclusion t ⁻¹' FailureOfSemipositiveMetricExtension.GlobalLineBundle.baseSet i

theorem baseSet_isOpen (t : ℂ) (i : Index) : IsOpen (baseSet t i) :=
  (FailureOfSemipositiveMetricExtension.GlobalLineBundle.baseSet_isOpen i).preimage (FixedFiber.inclusion_continuous t)

def gain (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) (i j : Index) (p : Fiber t) : ℂ :=
  FailureOfSemipositiveMetricExtension.GlobalLineBundle.gain a b i j (FixedFiber.inclusion t p)

theorem gain_self (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) (i : Index) (p : Fiber t) :
    gain t a b i i p = 1 := FailureOfSemipositiveMetricExtension.GlobalLineBundle.gain_self a b i _

theorem gain_comp (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) (i j k : Index) (p : Fiber t)
    (hp : p ∈ baseSet t i ∩ baseSet t j ∩ baseSet t k) :
    gain t a b j k p * gain t a b i j p = gain t a b i k p :=
  FailureOfSemipositiveMetricExtension.GlobalLineBundle.gain_comp a b i j k _ hp

theorem gain_continuousOn (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) (i j : Index) :
    ContinuousOn (gain t a b i j) (baseSet t i ∩ baseSet t j) :=
  (FailureOfSemipositiveMetricExtension.GlobalLineBundle.gain_continuousOn a b i j).comp
    (FixedFiber.inclusion_continuous t).continuousOn (fun _ hp => hp)

/-- The genuine line bundle on the actual fixed fibre, with the pulled-back cocycle. -/
def core (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) : VectorBundleCore ℂ (Fiber t) ℂ Index where
  baseSet := baseSet t
  isOpen_baseSet := baseSet_isOpen t
  indexAt p := (FailureOfSemipositiveMetricExtension.GlobalLineBundle.core a b).indexAt (FixedFiber.inclusion t p)
  mem_baseSet_at p := (FailureOfSemipositiveMetricExtension.GlobalLineBundle.core a b).mem_baseSet_at _
  coordChange i j p := gain t a b i j p • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i p _ v := by simp [gain_self]
  continuousOn_coordChange i j := (gain_continuousOn t a b i j).smul continuousOn_const
  coordChange_comp i j k p hp v := by
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
    rw [← mul_assoc,gain_comp t a b i j k p hp]

@[simp] theorem core_coordChange (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) (i j : Index) (p : Fiber t) :
    (core t a b).coordChange i j p =
      (FailureOfSemipositiveMetricExtension.GlobalLineBundle.core a b).coordChange i j (FixedFiber.inclusion t p) := rfl

theorem fiber_finrank (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) (p : Fiber t) :
    Module.finrank ℂ ((core t a b).Fiber p) = 1 := Module.finrank_self ℂ

theorem actual_vectorBundle (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) :
    VectorBundle ℂ ℂ (core t a b).Fiber := inferInstance

theorem gain_contMDiffOn (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) (i j : Index) (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) n (gain t a b i j) (baseSet t i ∩ baseSet t j) :=
  (FailureOfSemipositiveMetricExtension.GlobalLineBundle.gain_contMDiffOn a b i j n).comp
    (FixedFiber.inclusion_contMDiff t n).contMDiffOn (fun _ hp => hp)

instance core_isContMDiff (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) (n : WithTop ℕ∞) :
    (core t a b).IsContMDiff 𝓘(ℂ,FixedFiber.Coord) n where
  contMDiffOn_coordChange i j := (gain_contMDiffOn t a b i j n).smul contMDiffOn_const

theorem actual_analytic_vectorBundle (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) :
    ContMDiffVectorBundle ω ℂ (core t a b).Fiber 𝓘(ℂ,FixedFiber.Coord) := inferInstance

/-- Fibrewise identification with the original global line over the included point. -/
def fiberEquiv (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) (p : Fiber t) :
    (core t a b).Fiber p ≃L[ℂ]
      (FailureOfSemipositiveMetricExtension.GlobalLineBundle.core a b).Fiber (FixedFiber.inclusion t p) :=
  ContinuousLinearEquiv.refl ℂ ℂ

/-- Canonical map from the fixed-fibre line-bundle total space to the global one. -/
def bundleLift (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) :
    (core t a b).TotalSpace → (FailureOfSemipositiveMetricExtension.GlobalLineBundle.core a b).TotalSpace :=
  fun z => ⟨FixedFiber.inclusion t z.proj,fiberEquiv t a b z.proj z.2⟩

@[simp] theorem bundleLift_projects (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) (z : (core t a b).TotalSpace) :
    (bundleLift t a b z).proj = FixedFiber.inclusion t z.proj := rfl

/-- The canonical lift is exactly identity on the scalar coordinate in every matching trivialization. -/
theorem bundleLift_localTriv (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) (i : Index)
    (z : (core t a b).TotalSpace) :
    (FailureOfSemipositiveMetricExtension.GlobalLineBundle.core a b).localTriv i (bundleLift t a b z) =
      (FixedFiber.inclusion t z.proj,((core t a b).localTriv i z).2) := rfl

/-- The canonical total-space lift is a genuine complex analytic bundle map. -/
theorem bundleLift_contMDiff (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) (n : WithTop ℕ∞) :
    ContMDiff (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) (𝓘(ℂ,ChartCoord).prod 𝓘(ℂ)) n
      (bundleLift t a b) := by
  intro z
  let i := (core t a b).indexAt z.proj
  let ef := (core t a b).localTriv i
  let eg := (FailureOfSemipositiveMetricExtension.GlobalLineBundle.core a b).localTriv i
  haveI : MemTrivializationAtlas ef := ⟨⟨i,rfl⟩⟩
  haveI : MemTrivializationAtlas eg := ⟨⟨i,rfl⟩⟩
  have hz : z ∈ ef.source := (core t a b).mem_baseSet_at z.proj
  have hzg : bundleLift t a b z ∈ eg.source := (core t a b).mem_baseSet_at z.proj
  apply (eg.contMDiffAt_iff hzg).mpr
  constructor
  · exact (FixedFiber.inclusion_contMDiff t n).contMDiffAt.comp z
      (Bundle.contMDiffAt_proj (core t a b).Fiber)
  · have he : ContMDiffAt (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ))
        (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) n ef z :=
      ef.contMDiffOn.contMDiffAt (ef.open_source.mem_nhds hz)
    apply he.snd.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun w => congrArg Prod.snd (bundleLift_localTriv t a b i w))

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
