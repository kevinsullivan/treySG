import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Basic

namespace TreySG.SG

structure Node : Type where
(id : Nat)
deriving Repr

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
deriving Repr

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
deriving Repr

inductive ColorType
| Green
| Yellow
| Red
deriving Repr

inductive AttributeType
| Speed
| Color
deriving Repr

-- def AttributeValueType := (Sum Nat ColorType)
inductive AttributeValueType
| num (n : Nat)
| color (c : ColorType)
deriving Repr

open SemanticRelation
open EntityType
open ColorType
open AttributeType

def attrIsZero : AttributeValueType → Bool :=
  λ x => match x with
    | AttributeValueType.num n => n == 0
    | AttributeValueType.color _ => false

structure SceneGraph : Type 1 where

-- entities
(ego : Node)
(others : Set Node)
(egoInvariant : ego ∉ others)
(nodes : Set Node := { ego } ∪ others)

-- node types
(kind: Node → EntityType)

-- attributes
(attr: Node → AttributeType → AttributeValueType)

-- relations
(hasRel : Node → Node → SemanticRelation → Bool)

-- Graph Query Functions
(relSet (relSetNodes : Set Node) (relation : SemanticRelation) : Set Node :=
 { o ∈ nodes | ∃ n ∈ relSetNodes, hasRel n o relation})

(filterByAttribute (filterNodes : Set Node) (attrType : AttributeType) (filterFn : AttributeValueType → Bool) : Set Node :=
 { o ∈ filterNodes | filterFn (attr o attrType)})

(allOfType (type : EntityType) := {n ∈ nodes | kind n = type})

-- Properties
(hasStop: Prop := ((relSet {ego} IsIn) ∩ (relSet (allOfType StopSign) Controls)) ≠ ∅)
-- for some reason inlining the lambda from attrIsZero didn't work here, so it's defined separately
(isStopped : Prop := (filterByAttribute {ego} Speed attrIsZero) ≠ ∅)

end TreySG.SG
