#lang forge/froglet

// First pass model for Brown-style housing lottery.
// This captures:
//  - students partitioned by rising class year
//  - lottery-number bands by class year
//  - non-empty groups of size 1..6
//  - ranked buildings and ranked rooms
//  - complete housing assignment where nobody exceeds room capacity
//  - a lightweight ordering approximation: earlier lottery groups begin housing
//    no later than later lottery groups

abstract sig Year {}
one sig Senior, Junior, Sophomore extends Year {}

sig Group {
	pickNumber: one Int
}

sig Student {
	year: one Year,
	lotteryNumber: one Int,
	group: one Group,
	room: one Room
}

sig Building {
	buildingRank: one Int
}

sig Room {
	building: one Building,
	roomRank: one Int,
	capacity: one Int
}

pred lotteryBands {
	all s: Student | {
		s.year = Senior implies (s.lotteryNumber >= 1 and s.lotteryNumber <= 5)
		s.year = Junior implies (s.lotteryNumber >= 6 and s.lotteryNumber <= 10)
		s.year = Sophomore implies (s.lotteryNumber >= 11 and s.lotteryNumber <= 15)
	}
}

pred groupsWellformed {
	// Everyone is in exactly one group by signature.
	// No empty groups + group size in [1, 6].
	all g: Group | {
		some s: Student | s.group = g
		# { s: Student | s.group = g } <= 6
	}

	// First pass simplification: each group shares one lottery slot.
	all s: Student | s.lotteryNumber = s.group.pickNumber

	// Strict slot order among groups.
	all disj g1, g2: Group | g1.pickNumber != g2.pickNumber
}

pred inventoryWellformed {
	// 45 ranked buildings.
	#Building = 45
	all b: Building | b.buildingRank >= 1 and b.buildingRank <= 45
	all disj b1, b2: Building | b1.buildingRank != b2.buildingRank

	// Rooms have capacities 1..6 and unique global rank.
	all r: Room | {
		r.capacity >= 1 and r.capacity <= 6
		r.roomRank >= 1
	}
	all disj r1, r2: Room | r1.roomRank != r2.roomRank

	// Building rank induces room-rank order (all rooms in earlier buildings
	// appear before all rooms in later buildings).
	all r1, r2: Room |
		r1.building.buildingRank < r2.building.buildingRank implies
			r1.roomRank < r2.roomRank
}

pred assignmentWellformed {
	// All students are housed by signature (each student has exactly one room).

	// No room is overfilled.
	all r: Room |
		# { s: Student | s.room = r } <= r.capacity

	// Rooms are not shared across multiple original groups in this first pass.
	all r: Room |
		all s1, s2: Student |
			(s1.room = r and s2.room = r) implies s1.group = s2.group
}

pred groupStartsNoLaterThanLaterGroups {
	// Approximate pick-order behavior:
	// if g1 has an earlier pick number than g2, then the first room used by g1
	// is no later than the first room used by g2.
	all disj g1, g2: Group |
		g1.pickNumber < g2.pickNumber implies {
			some r1: Room | {
				some s1: Student | s1.group = g1 and s1.room = r1
				all s1: Student | s1.group = g1 implies r1.roomRank <= s1.room.roomRank

				some r2: Room | {
					some s2: Student | s2.group = g2 and s2.room = r2
					all s2: Student | s2.group = g2 implies r2.roomRank <= s2.room.roomRank
					r1.roomRank <= r2.roomRank
				}
			}
		}
}

pred firstPassHousingLottery {
	lotteryBands
	groupsWellformed
	inventoryWellformed
	assignmentWellformed
	groupStartsNoLaterThanLaterGroups
}

// Tiny sanity scope (for quick iteration)
run {firstPassHousingLottery}
for exactly 45 Building, exactly 20 Room, exactly 24 Student, exactly 8 Group, 7 Int

// A stronger scope if the tiny scope is satisfiable on your machine:
// run {firstPassHousingLottery}
// for exactly 45 Building, exactly 70 Room, exactly 120 Student, exactly 35 Group, 7 Int

