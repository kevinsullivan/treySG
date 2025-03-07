-- import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic

namespace TreySG.SG

structure Node : Type where
(id : String)
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
-- Catchall
| None
| Unknown
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
-- Catchall
| Unknown
| Bot
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
| None
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
    | AttributeValueType.None => false

structure SceneGraph : Type 1 where
-- entities
(ego : Node)
(others : NodeSet)
-- node types
(kind: Node → EntityType)
-- attributes
(attr: Node → AttributeType → AttributeValueType)
-- relations
(hasRel : Node → Node → SemanticRelation → Bool)


def sg_nodes (sg : SceneGraph) : NodeSet := {sg.ego} ∪ sg.others

-- Graph Query Functions
def relSet (sg : SceneGraph) (relSetNodes : NodeSet) (relation : SemanticRelation) : NodeSet :=
 { o ∈ sg_nodes sg | ∃ n ∈ relSetNodes, sg.hasRel n o relation}

def filterByAttribute (sg : SceneGraph) (filterNodes : NodeSet) (attrType : AttributeType) (filterFn : AttributeValueType → Bool) : NodeSet :=
 { o ∈ filterNodes | filterFn (sg.attr o attrType)}

def allOfType (sg : SceneGraph) (type : EntityType) := {n ∈ sg_nodes sg | sg.kind n == type}

-- Properties
-- These should probably be Prop, but doing that made LTLf.lean sad bc it said it wasn't decidable
-- I don't follow how it's decidable here, but it isn't decidable within LTLf.lean
def hasStop (sg : SceneGraph) : Bool := ((relSet sg {sg.ego} IsIn) ∩ (relSet sg (allOfType sg StopSign) Controls)) ≠ ∅
-- for some reason inlining the lambda from attrIsZero didn't work here, so it's defined separately
def isStopped (sg : SceneGraph) : Bool := (filterByAttribute sg {sg.ego} Speed attrIsZero) ≠ ∅

end TreySG.SG
