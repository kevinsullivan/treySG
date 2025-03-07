import Mathlib.Data.Finset.Basic
import TreySG.SGTrey
import TreySG.LTLf

namespace TreySG.SG

def ego : Node := ⟨"ego"⟩
def egoLane : Node := ⟨"Ego Lane"⟩
def opposingLane : Node := ⟨"Opposing Lane"⟩
def car1 : Node := ⟨"Car 1"⟩
def car2 : Node := ⟨"Car 2"⟩
def stopSign : Node := ⟨"Stop Sign"⟩

def othersWithStop : NodeSet := {egoLane, opposingLane, car1, car2, stopSign}

def othersNoStop : NodeSet := {egoLane, opposingLane, car1, car2}

def kind (node : Node) : EntityType :=
match node.id with
| "ego" => EntityType.Car
| "Ego Lane" => EntityType.Lane
| "Opposing Lane" => EntityType.Lane
| "Car 1" => EntityType.Car
| "Car 2" => EntityType.Car
| "Stop Sign" => EntityType.StopSign
| _ => EntityType.Bot

def attributes (node : Node) (attrType : AttributeType) : AttributeValueType :=
match (node.id, attrType) with
| ("ego", AttributeType.Speed) => AttributeValueType.num 2
| (_, _) => AttributeValueType.None


def egoStoppedAttributes (node : Node) (attrType : AttributeType) : AttributeValueType :=
match (node.id, attrType) with
| ("ego", AttributeType.Speed) => AttributeValueType.num 0
| (_, _) => AttributeValueType.None


def relations (node1 : Node) (node2 : Node) (rel : SemanticRelation) : Bool :=
match (node1.id, node2.id, rel) with
| ("ego", "Ego Lane", SemanticRelation.IsIn) => true
| ("Stop Sign", "Ego Lane", SemanticRelation.Controls) => true
| (_,_,_) => false


def sgWithStopEgoGo : SceneGraph := TreySG.SG.SceneGraph.mk ego othersWithStop kind attributes relations
def sgNoStopEgoGo : SceneGraph := TreySG.SG.SceneGraph.mk ego othersNoStop kind attributes relations
def sgWithStopEgoStop : SceneGraph := TreySG.SG.SceneGraph.mk ego othersWithStop kind egoStoppedAttributes relations

def exampleViolatingStopSign : SGTrace := [sgNoStopEgoGo, sgWithStopEgoGo, sgNoStopEgoGo]
def exampleStoppingAtStopSign : SGTrace := [sgNoStopEgoGo, sgWithStopEgoGo, sgWithStopEgoStop, sgNoStopEgoGo]

-- Ego doesn't stop, violation
#eval satisfyingSGTrace exampleViolatingStopSign stopAtStopSigns

-- Ego stops, satisfying
#eval satisfyingSGTrace exampleStoppingAtStopSign stopAtStopSigns

end TreySG.SG
