import Mathlib.Topology.MetricSpace.PseudoMetric
import TreeRewritingGame.OrdinaryDisplay
import TreeRewritingGame.MaskedDisplay
import ProofWidgets

open ProofWidgets 

lemma unionOfOpenIsOpen [PseudoMetricSpace X] {A B : Set X}
  (hA : IsOpen A) (hB : IsOpen B) : IsOpen (A ∪ B) := by 
  with_panel_widgets[GoalTypePanel]
  revert hA hB
  intros hA hB
  rw [Metric.isOpen_iff]
  revert hA hB
  sorry
