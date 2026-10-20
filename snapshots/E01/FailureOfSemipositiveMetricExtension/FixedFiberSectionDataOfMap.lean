import FailureOfSemipositiveMetricExtension.GlobalFiberSections
import FailureOfSemipositiveMetricExtension.FixedFiberAdjointIsomorphism

/-! Every actual analytic section map determines the verified scalar transition
data, and arbitrary genuine adjoint sections transfer through the actual
canonical-factor bundle isomorphism. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

def sectionDataOfAnalyticMap {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ}
    (s : ∀ p : Fiber t, (core t a b).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (core t a b).TotalSpace))) : SectionData t a b where
  coefficient i p := ((core t a b).localTriv i ⟨p,s p⟩).2
  analytic i := by
    let e := (core t a b).localTriv i
    haveI : MemTrivializationAtlas e := ⟨⟨i,rfl⟩⟩
    have hh : ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
        (fun p => e (⟨p,s p⟩ : (core t a b).TotalSpace)) (baseSet t i) :=
      e.contMDiffOn.comp hs.contMDiffOn (fun p hp => hp)
    exact contMDiff_snd.comp_contMDiffOn hh
  compatible i j p hp := by
    change gain t a b i j p * (gain t a b ((core t a b).indexAt p) i p * (show ℂ from s p)) =
      gain t a b ((core t a b).indexAt p) j p * (show ℂ from s p)
    rw [← mul_assoc,gain_comp t a b ((core t a b).indexAt p) i j p
      ⟨⟨(core t a b).mem_baseSet_at p,hp.1⟩,hp.2⟩]

@[simp] theorem sectionDataOfAnalyticMap_value {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ}
    (s : ∀ p : Fiber t, (core t a b).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (core t a b).TotalSpace))) (p : Fiber t) :
    sectionValue (sectionDataOfAnalyticMap s hs) p = s p := by
  change gain t a b ((core t a b).indexAt p) ((core t a b).indexAt p) p * (show ℂ from s p) = s p
  rw [gain_self,one_mul]

def ambientDataOfAdjointMap (t : ℂ) (m : ℕ)
    (s : ∀ p : Fiber t, (adjointCore t m).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (adjointCore t m).TotalSpace))) :
    SectionData t (1-2*(m:ℤ)) (fun _ => (m:ℤ)-1) :=
  sectionDataOfAnalyticMap (fun p => (adjointFiberEquiv t m p).symm (s p))
    ((adjointBundleEquiv_symm_contMDiff t m).comp hs)

@[simp] theorem ambientDataOfAdjointMap_value (t : ℂ) (m : ℕ)
    (s : ∀ p : Fiber t, (adjointCore t m).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (adjointCore t m).TotalSpace))) (p : Fiber t) :
    sectionValue (ambientDataOfAdjointMap t m s hs) p = (adjointFiberEquiv t m p).symm (s p) :=
  sectionDataOfAnalyticMap_value _ _ p

/-- The arbitrary actual adjoint coefficient includes exactly the genuine
nowhere-zero canonical factor, in every actual refined coordinate frame. -/
theorem ambientDataOfAdjointMap_coefficient (t : ℂ) (m : ℕ)
    (s : ∀ p : Fiber t, (adjointCore t m).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (adjointCore t m).TotalSpace)))
    (d : DivisionIndex) (p : Fiber t) (hp : p ∈ divisionPatch t d) :
    ((adjointCore t m).localTriv d ⟨p,s p⟩).2 =
      canonicalFactor t d p * (ambientDataOfAdjointMap t m s hs).coefficient (divisionFrame d) p := by
  have h := adjointBundleEquiv_localTriv t m d
    ((adjointBundleEquiv t m).symm ⟨p,s p⟩) hp
  rw [Equiv.apply_symm_apply] at h
  exact congrArg Prod.snd h

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
