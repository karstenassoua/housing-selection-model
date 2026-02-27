#lang forge/froglet


// What is a housing lottery
// We have a bunch of students
// We give them all random numbers within a 5-num range
// - Seniors get numbers 1, 2, 3, 4, 5
// - Juniors get numbers 6, 7, 8, 9, 10
// - Sophomores get numbers 11, 12, 13, 14, 15
// - No freshmen obviously

// I dont know if we can do enums in forge but if we have to represent class year as a string or int thats fine too.
// Also for the duration of this project every class year is assumed to be refering to the rising class, so "Junior" means "rising Junior" and so on.

// Everyone gets numbers, everyone is in a group. 
// There are no empty groups. 
// Some groups contain 1 person. Groups can contain 1-6 people.

// After checking that everyone is in groups, we distribute the housing in terms of slot order. 
// There are 45 buildings on campus, and they are strictly rank ordered such that everyone with the first housing slot will take the rooms in building 1 that fit their group size.

// Example: 
// If we have students [1 1 1] [2 2] [2] [3 3 3 3] [4 4] [5 5 5]
// And Dorm 1 has rooms with size 3, 2, 2, 1
// Group 1 will fill Room 1 with 3 people, Group 2 will fill Room 2 with 2 people, Group 2 will fill Room 4 with 1 person, and Group 4 will fill Room 3 with 2 people.
// Groups may fill rooms that they are too small for but not rooms that they are too large for.

/// The filling process continues.
// If a 2 person group is too big to fit in the next available room, they skip that room and try the next one. 
// If there are no more rooms available, their group fractures one member at a time until they can fit in the next available room.

// If a 1 person group is too big to fit in any available room (there are no singles left) they are merged with any remaining groups until they can fit in the next available room, starting with the smallest group first.

// The housing process ends when all students are housed. All students must be housed


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
	#Building = 5
	all b: Building | b.buildingRank >= 1 and b.buildingRank <= 5
	all disj b1, b2: Building | b1.buildingRank != b2.buildingRank

	// Rooms have capacities 1..6 and unique global rank.
	all r: Room | {
		r.capacity >= 1 and r.capacity <= 6
		r.roomRank >= 1
	}
	all disj r1, r2: Room | r1.roomRank != r2.roomRank

	// Ensure at least two rooms have different capacities
    some disj r1, r2: Room | r1.capacity != r2.capacity
	// Ensure at least one room of each capacity exists
	all cap: Int | (cap >= 1 and cap <= 6) implies {
        some r: Room | r.capacity = cap
    }

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

run {firstPassHousingLottery}
for 5 Int, exactly 5 Building, exactly 10 Room, exactly 12 Student, exactly 4 Group

// Tiny sanity scope (for quick iteration)
// run {firstPassHousingLottery}
// for 7 Int, exactly 45 Building, exactly 20 Room, exactly 24 Student, exactly 8 Group

// A stronger scope if the tiny scope is satisfiable on your machine:
// run {firstPassHousingLottery}
// for exactly 45 Building, exactly 70 Room, exactly 120 Student, exactly 35 Group, 7 Int

