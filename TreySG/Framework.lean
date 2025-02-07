-- UNDER CONSTRUCTION

structure World : Type where
(uid : Nat)

def aWorld := World.mk 0

structure WorldRep (w : World) : Type where
(f : Nat)

def aWorldRep := WorldRep aWorld

def perceive : (w : World) → (WorldRep w) := sorry

-- We need The World Monad
def perception := perceive aWorld

def aWorldRep := perceive aWorld

abbrev WorldDom := WorldRep

def specLang := Type

#check WorldDom

abbrev Property := WorldDom → Prop


def StateSpace : Type := List Property
