import FailureOfSemipositiveMetricExtension.GermIdealSheaves

/-! Membership in a principal holomorphic stalk ideal is equivalent to genuine
local divisibility by a holomorphic function on some open neighbourhood. -/
namespace FailureOfSemipositiveMetricExtension.Multiplier
noncomputable section
open Set TopologicalSpace Opposite CategoryTheory Manifold
open scoped Manifold ContDiff

variable (M : Type) [TopologicalSpace M] [ChartedSpace Coord M]

/-- A sheaf-theoretic local-ring membership statement is connected to actual
nearby holomorphic sections, not merely to formal divisibility in an abstract ring. -/
theorem germ_mem_power_iff_locally_divisible (U : Opens M)
    (d f : C^∞⟮𝓘(ℂ,Coord),U;𝓘(ℂ),ℂ⟯) (p : M) (hp : p ∈ U) (k : ℕ) :
    (sheaf M).presheaf.germ U p hp f ∈
      Ideal.span {((sheaf M).presheaf.germ U p hp d)^k} ↔
    ∃ (V : Opens M) (hpV : p ∈ V) (i : V ⟶ U)
      (a : C^∞⟮𝓘(ℂ,Coord),V;𝓘(ℂ),ℂ⟯),
      (sheaf M).presheaf.map i.op f = (show C^∞⟮𝓘(ℂ,Coord),V;𝓘(ℂ),ℂ⟯ from (sheaf M).presheaf.map i.op d)^k * a := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨a,ha⟩
    obtain ⟨V,hpV,s,hs⟩ := (sheaf M).presheaf.germ_exist p a
    let W : Opens M := U ⊓ V
    have hpW : p ∈ W := ⟨hp,hpV⟩
    let i : W ⟶ U := homOfLE inf_le_left
    let j : W ⟶ V := homOfLE inf_le_right
    let dW := (sheaf M).presheaf.map i.op d
    let fW := (sheaf M).presheaf.map i.op f
    let sW := (sheaf M).presheaf.map j.op s
    have hW : (sheaf M).presheaf.germ W p hpW fW =
        (sheaf M).presheaf.germ W p hpW (dW^k*sW) := by
      rw [map_mul,map_pow]
      dsimp only [fW,dW,sW]
      rw [(sheaf M).presheaf.germ_res_apply i p hpW,
        (sheaf M).presheaf.germ_res_apply i p hpW,
        (sheaf M).presheaf.germ_res_apply j p hpW,hs]
      exact ha
    obtain ⟨Z,hpZ,iZ,jZ,hZ⟩ := (sheaf M).presheaf.germ_eq p hpW hpW fW (dW^k*sW) hW
    have hij : iZ = jZ := Subsingleton.elim _ _
    subst jZ
    refine ⟨Z,hpZ,iZ ≫ i,(sheaf M).presheaf.map iZ.op sW,?_⟩
    rw [map_mul,map_pow] at hZ
    simpa only [dW,fW,Functor.map_comp,ConcreteCategory.comp_apply] using hZ
  · rintro ⟨V,hpV,i,a,ha⟩
    refine ⟨(sheaf M).presheaf.germ V p hpV a,?_⟩
    have h := congrArg ((sheaf M).presheaf.germ V p hpV) ha
    rw [map_mul,map_pow,(sheaf M).presheaf.germ_res_apply i p hpV,
      (sheaf M).presheaf.germ_res_apply i p hpV] at h
    exact h

end
end FailureOfSemipositiveMetricExtension.Multiplier
