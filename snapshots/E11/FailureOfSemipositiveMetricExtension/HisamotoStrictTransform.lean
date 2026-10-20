import FailureOfSemipositiveMetricExtension.HisamotoFibreGeometry
import FailureOfSemipositiveMetricExtension.HisamotoBlowdownComplement

/-! The ruling fibre is the strict transform of the actual projective line
through the blown-up point: the closure defining a strict transform is
computed in the actual incidence topology. -/
namespace FailureOfSemipositiveMetricExtension.Hisamoto
noncomputable section
open Set Topology

/-- The actual linear two-plane whose projectivization is the line through
`[1:0:0]` with direction `d`. -/
def linePlane (d : Direction) : Submodule ℂ (Fin 3 → ℂ) := d.submodule.comap centrePair

theorem linePlane_eq_range (i : Fin 2) (t : ℂ) :
    linePlane (ProjectiveLine.param i t) = LinearMap.range (fiberLinear i t) := by
  ext v
  change centrePair v ∈ (ProjectiveLine.param i t).submodule ↔ _
  rw [← directionVector_mk i t,Projectivization.submodule_mk,Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨![v 0,a],?_⟩
    ext j
    fin_cases j
    · rfl
    · exact congrFun ha 0
    · exact congrFun ha 1
  · rintro ⟨w,rfl⟩
    refine ⟨w 1,?_⟩
    ext j
    fin_cases j <;> simp [centrePair,fiberLinear,smul_eq_mul]

theorem linePlane_finrank (d : Direction) : Module.finrank ℂ (linePlane d) = 2 := by
  obtain ⟨i,t,rfl⟩ := ProjectiveLine.charts_cover d
  rw [linePlane_eq_range]
  have he := LinearEquiv.ofInjective (fiberLinear i t) (fiberLinear_injective i t)
  simpa using he.finrank_eq.symm

/-- Points of the genuine projectivization of the two-dimensional linear subspace. -/
def lineThrough (d : Direction) : Set PlanePoint := {p | p.submodule ≤ linePlane d}

theorem lineThrough_eq_range (i : Fin 2) (t : ℂ) :
    lineThrough (ProjectiveLine.param i t) = range (fiberPlane i t) := by
  ext p
  exact ⟨exists_fiberPlane_of_incidence i t p,fun ⟨q,hq⟩ => hq ▸ fiberPlane_incidence i t q⟩

/-- Strict transform means closure of the inverse image away from the centre. -/
def strictTransform (d : Direction) : Set Point :=
  closure (blowdown ⁻¹' (lineThrough d \ {centre}))

theorem strictTransform_punctured_preimage (d : Direction) :
    blowdown ⁻¹' (lineThrough d \ {centre}) = {q | ruling q = d} ∩ awayCentre := by
  ext q
  constructor
  · rintro ⟨hq,hc⟩
    have hn : blowdown q ≠ centre := hc
    exact ⟨(incidence_unique_away _ hn _ q.property).trans
      (incidence_unique_away _ hn d hq).symm,hn⟩
  · rintro ⟨hd,hn⟩
    exact ⟨by change Incidence (blowdown q) d; rw [← hd]; exact q.property,hn⟩

theorem ruling_fibre_isClosed (d : Direction) : IsClosed {q : Point | ruling q = d} :=
  isClosed_eq ruling_continuous continuous_const

/-- The exceptional point on the fibre is approached by its punctured affine line. -/
theorem exceptional_fibre_point_mem_closure (i : Fin 2) (t : ℂ) :
    localParam i (ProjectiveLine.param 0 0,t) ∈
      closure ({q : Point | ruling q = ProjectiveLine.param i t} ∩ awayCentre) := by
  let f : ℂ → Point := fun s => localParam i (ProjectiveLine.param 0 s,t)
  have hf : Continuous f := (localParam_continuous i).comp
    ((ProjectiveLine.param_continuous 0).prodMk continuous_const)
  have hzero : (0 : ℂ) ∈ closure ({0}ᶜ : Set ℂ) := (dense_compl_singleton 0) 0
  apply closure_mono (s := f '' ({0}ᶜ : Set ℂ)) ?_ (mem_closure_image hf.continuousAt hzero)
  rintro q ⟨s,hs,rfl⟩
  refine ⟨rfl,?_⟩
  change localParam i (ProjectiveLine.param 0 s,t) ∉ exceptionalSet
  rw [fibre_exceptional_iff]
  exact fun he => hs ((ProjectiveLine.param_injective 0) he)

/-- Exact identification with the entire ruling fibre, including the point on E. -/
theorem strictTransform_eq_ruling_fibre (d : Direction) :
    strictTransform d = {q : Point | ruling q = d} := by
  rw [strictTransform,strictTransform_punctured_preimage]
  apply subset_antisymm (closure_minimal inter_subset_left (ruling_fibre_isClosed d))
  intro q hq
  by_cases hn : blowdown q ≠ centre
  · exact subset_closure ⟨hq,hn⟩
  · obtain ⟨i,t,rfl⟩ := ProjectiveLine.charts_cover d
    change ruling q = ProjectiveLine.param i t at hq
    have hr : q ∈ rulingChart i := ⟨t,hq.symm⟩
    have he := localParam_localCoordinates i q hr
    have ht : (localCoordinates i q).2 = t := by simp [localCoordinates,hq]
    have hp : (localCoordinates i q).1 = ProjectiveLine.param 0 0 := by
      apply (fibre_exceptional_iff i t _).mp
      change blowdown (localParam i ((localCoordinates i q).1,t)) = centre
      rw [← ht,he]
      exact not_ne_iff.mp hn
    have hqeq : q = localParam i (ProjectiveLine.param 0 0,t) := by
      rw [← hp,← ht]; exact he.symm
    rw [hqeq]
    exact exceptional_fibre_point_mem_closure i t

end
end FailureOfSemipositiveMetricExtension.Hisamoto
