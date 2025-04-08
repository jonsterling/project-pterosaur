import Std.Data.HashMap

-- Inspired by https://github.com/PeterKementzey/graph-library-for-lean4/blob/master/Graph/Graph.lean

structure Edge (α : Type u) (β : Type v) where
  target : α
  label : β

structure Graph (α : Type u) [BEq α] [Hashable α] (β : Type v) where
  vertices : Std.HashMap α (Array (Edge α β))

namespace Graph
  variable {α : Type} [BEq α] [Hashable α] {β : Type}

  def empty : Graph α β := ⟨{}⟩

  def addVertex (g : Graph α β) (vertex : α) : Graph α β :=
    { g with vertices := g.vertices.insertIfNew vertex #[] }

  def addEdge (g : Graph α β) (source target : α) (label : β) : Graph α β := {
    g with vertices :=
      g.vertices.modify source λ fan =>
      fan.push ⟨target, label⟩
  }

  def successors (g : Graph α β) (vtx : α) : Array α :=
    g.vertices[vtx]!.map Edge.target

  def predecessors (g : Graph α β) (vtx : α) : Array α :=
    let χ (edge : Edge α β) : Bool := edge.target == vtx
    Id.run do
      let mut res : Array α := #[]
      for ⟨x, fan⟩ in g.vertices do
        if Option.isSome $ fan.find? χ then
          res := res.push x
      return res
end Graph
