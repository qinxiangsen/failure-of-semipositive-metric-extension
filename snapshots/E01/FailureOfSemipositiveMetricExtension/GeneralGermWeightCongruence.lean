import FailureOfSemipositiveMetricExtension.GeneralGermLocalIntegrability

/-! The true integrability stalk is insensitive to changes of weight outside
the neighbourhood on which its actual holomorphic representative is defined. -/
namespace FailureOfSemipositiveMetricExtension.GeneralMultiplier
noncomputable section
open Set MeasureTheory TopologicalSpace Manifold
open scoped Manifold ContDiff ENNReal

variable (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Coord n) M]

theorem integrableGerm_section_congr_weight (m : ℕ) (w w' : M → WithBot ℝ)
    (U : Opens M) (f : C^∞⟮𝓘(ℂ,Coord n),U;𝓘(ℂ),ℂ⟯) (p : M) (hp : p ∈ U)
    (hw : EqOn w w' U) :
    IntegrableGerm n M m w p ((sheaf n M).presheaf.germ U p hp f) ↔
      IntegrableGerm n M m w' p ((sheaf n M).presheaf.germ U p hp f) := by
  suffices hforward : ∀ (u u' : M → WithBot ℝ), EqOn u u' U →
      IntegrableGerm n M m u p ((sheaf n M).presheaf.germ U p hp f) →
      IntegrableGerm n M m u' p ((sheaf n M).presheaf.germ U p hp f) from
    ⟨hforward w w' hw,hforward w' w hw.symm⟩
  intro u u' hu hg
  obtain ⟨e,hpe,r,hr,hsub,hfinite⟩ := integrableGerm_local_representative n M m u U f p hp hg
  refine ⟨U,hp,f,rfl,e,hpe,r,hr,hsub,?_⟩
  have he : (∫⁻ z in Metric.closedBall (e.chart p) r,
      ENNReal.ofReal (Complex.normSq (sectionFunction n M U f (e.chart.symm z))) *
        Multiplier.exponentialWeight (u' (e.chart.symm z)) ^ m ∂volume) =
      ∫⁻ z in Metric.closedBall (e.chart p) r,
      ENNReal.ofReal (Complex.normSq (sectionFunction n M U f (e.chart.symm z))) *
        Multiplier.exponentialWeight (u (e.chart.symm z)) ^ m ∂volume := by
    apply setLIntegral_congr_fun measurableSet_closedBall
    filter_upwards [] with z hz
    rw [hu (hsub hz).2]
  rwa [he]

end
end FailureOfSemipositiveMetricExtension.GeneralMultiplier
