-- import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic

namespace TreySG.SG

structure Node : Type where
(id : Nat)
deriving Repr, BEq, DecidableEq, Hashable

inductive SemanticRelation
-- containment, e.g. entities in Lanes, Lanes in Roads, Roads in Intersections
| IsIn
-- Lane to Lanes
| Opposes
| TravelsTo
| LaneChange
-- Traffic Signs to Lanes
| Controls
-- General Left/Right Direction
| LeftOf
| RightOf
-- General Angular Direction
| DirectFrontOf
| SideFrontOf
| DirectRearOf
| SideRearOf
-- General Distances
| SafetyHazard
| NearCollision
| SuperNear
| VeryNear
| Near
| Visible
deriving Repr, BEq, DecidableEq

inductive EntityType
-- Road structures
| Junction
| Road
| Lane
-- Road Signals
| StopSign
| TrafficLight
-- Vehicles
| Car
| Truck
| Van
| Bus
| Motorcycle
| Bicycle
deriving Repr, BEq, DecidableEq

inductive ColorType
| Green
| Yellow
| Red
deriving Repr, BEq, DecidableEq

inductive AttributeType
| Speed
| Color
deriving Repr, BEq, DecidableEq

-- def AttributeValueType := (Sum Nat ColorType)
inductive AttributeValueType
| num (n : Nat)
| color (c : ColorType)
deriving Repr, BEq, DecidableEq

open SemanticRelation
open EntityType
open ColorType
open AttributeType

abbrev NodeSet := Finset Node

def attrIsZero : AttributeValueType → Bool :=
  λ x => match x with
    | AttributeValueType.num n => n == 0
    | AttributeValueType.color _ => false

structure SceneGraph : Type 1 where

-- entities
(ego : Node)
(egoSet : NodeSet := {ego})
(others : NodeSet)
(egoInvariant : ego ∉ others)
(nodes : NodeSet := egoSet ∪ others)

-- node types
(kind: Node → EntityType)

-- attributes
(attr: Node → AttributeType → AttributeValueType)

-- relations
(hasRel : Node → Node → SemanticRelation → Bool)

-- Graph Query Functions
(relSet (relSetNodes : NodeSet) (relation : SemanticRelation) : NodeSet :=
 { o ∈ nodes | ∃ n ∈ relSetNodes, hasRel n o relation})

(filterByAttribute (filterNodes : NodeSet) (attrType : AttributeType) (filterFn : AttributeValueType → Bool) : NodeSet :=
 { o ∈ filterNodes | filterFn (attr o attrType)})

(allOfType (type : EntityType) := {n ∈ nodes | kind n == type})

-- Properties
-- These should probably be Prop, but doing that made LTLf.lean sad bc it said it wasn't decidable
-- I don't follow how it's decidable here, but it isn't decidable within LTLf.lean
(hasStop: Bool := ((relSet {ego} IsIn) ∩ (relSet (allOfType StopSign) Controls)) ≠ ∅)
-- for some reason inlining the lambda from attrIsZero didn't work here, so it's defined separately
(isStopped : Bool := (filterByAttribute {ego} Speed attrIsZero) ≠ ∅)

end TreySG.SG
