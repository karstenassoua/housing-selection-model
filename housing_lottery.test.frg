#lang forge/froglet

open "housing_lottery.frg"

// This file is for testing our housing lottery model.

pred SeniorBands[s: Student] {
    s.year = Senior implies (s.lotteryNumber >= 1 and s.lotteryNumber <= 5)
}

pred JuniorBands[s: Student] {
    s.year = Junior implies (s.lotteryNumber >= 6 and s.lotteryNumber <= 10)
}

pred SophomoreBands[s: Student] {
    s.year = Sophomore implies (s.lotteryNumber >= 11 and s.lotteryNumber <= 15)
}

test suite for lotteryBands {
    -- assert lotteryBands is satisfiable for multiple
    assert lotteryBands is sat for 5 Int, 10 Student
    assert lotteryBands is sat for 7 Int, 24 Student
    -- check Senior bands are 1-5
    assert all s: Student | lotteryBands is sufficient for SeniorBands[s] for 5 Int
    assert all s: Student | SeniorBands[s] is necessary for lotteryBands for 5 Int
    -- check Junior bands are 6-10
    assert all s: Student | lotteryBands is sufficient for JuniorBands[s] for 5 Int
    assert all s: Student | JuniorBands[s] is necessary for lotteryBands for 5 Int
    -- check Sophomore bands are 11-15
    assert all s: Student | lotteryBands is sufficient for SophomoreBands[s] for 5 Int
    assert all s: Student | SophomoreBands[s] is necessary for lotteryBands for 5 Int
    -- example sat
    assert {
        lotteryBands
        some s: Student {
            s.year = Senior and s.lotteryNumber = 3
        }
    } is sat for 5 Int, 10 Student
    -- example unsat
    assert {
        lotteryBands
        some s: Student {
            s.year = Senior and s.lotteryNumber = 6
        }
    } is unsat for 5 Int, 10 Student
}

pred allStudentsInGroups[s: Student] {
    some g: Group {
        s.group = g
    }
}

pred noGroupTooBig[g: Group] {
    # { s: Student | s.group = g } <= 6
}

pred groupSharesLotterySlot[s: Student] {
    s.lotteryNumber = s.group.pickNumber
}

pred noGroupsShareLotterySlot[g1, g2: Group] {
    g1.pickNumber != g2.pickNumber
}

test suite for groupsWellformed {
    -- assert groupsWellformed is satisfiable
    assert groupsWellformed is sat for 5 Int, 10 Student, 4 Group
    assert groupsWellformed is sat for 7 Int, 24 Student, 8 Group
    -- check everyone is in a group
    assert all s: Student | groupsWellformed is sufficient for allStudentsInGroups[s] for 5 Int, 10 Student, 4 Group
    assert all s: Student | allStudentsInGroups[s] is necessary for groupsWellformed for 5 Int, 10 Student, 4 Group
    -- check no group is too big
    assert all g: Group | groupsWellformed is sufficient for noGroupTooBig[g] for 5 Int, 10 Student, 4 Group
    assert all g: Group | noGroupTooBig[g] is necessary for groupsWellformed for 5 Int, 10 Student, 4 Group
    -- check group shares lottery slot
    assert all s: Student | groupsWellformed is sufficient for groupSharesLotterySlot[s] for 5 Int, 10 Student, 4 Group
    assert all s: Student | groupSharesLotterySlot[s] is necessary for groupsWellformed for 5 Int, 10 Student, 4 Group
    -- check no groups share lottery slot
    assert all disj g1, g2: Group | groupsWellformed is sufficient for noGroupsShareLotterySlot[g1, g2] for 5 Int, 10 Student, 4 Group
    assert all disj g1, g2: Group | noGroupsShareLotterySlot[g1, g2] is necessary for groupsWellformed for 5 Int, 10 Student, 4 Group
    -- example sat
    assert {
        groupsWellformed
        some s: Student {
            s.group.pickNumber = 3
            s.lotteryNumber = 3
        }
    } is sat for 5 Int, 10 Student, 4 Group
    -- example unsat
    assert {
        groupsWellformed
        some disj g1, g2: Group {
            g1.pickNumber = g2.pickNumber
        }
    } is unsat for 5 Int, 10 Student, 4 Group
}

pred noRankingAboveNumberOfBuildings[b: Building] {
    b.buildingRank >= 1 and b.buildingRank <= #Building
}

pred noBuilingRankTies[b1, b2: Building] {
    b1.buildingRank != b2.buildingRank
}

pred roomsHaveValidCapacities[r: Room] {
    r.capacity >= 1 and r.capacity <= 6
}

pred roomsHaveValidRanks[r: Room] {
    r.roomRank >= 1
}

pred noRoomRankTies[r1, r2: Room] {
    r1.roomRank != r2.roomRank
}

pred roomsHaveDifferentCapacities[r1, r2: Room] {
    r1.capacity != r2.capacity
}

pred atLeastOneRoomOfEachCapacity[r1, r2, r3, r4, r5, r6: Room] {
    r1.capacity = 1 and r2.capacity = 2 and r3.capacity = 3 and r4.capacity = 4 and r5.capacity = 5 and r6.capacity = 6
}

pred buildingRankInducesRoomRankOrder[r1, r2: Room] {
    -- Building rank induces room-rank order
    r1.building.buildingRank < r2.building.buildingRank implies r1.roomRank < r2.roomRank
}

test suite for inventoryWellformed {
    -- assert inventoryWellformed is satisfiable
    assert inventoryWellformed is sat for 5 Int, exactly 5 Building, exactly 10 Room
    assert inventoryWellformed is sat for 7 Int, exactly 10 Building, exactly 20 Room
    -- check building ranks are valid
    assert all b: Building | inventoryWellformed is sufficient for noRankingAboveNumberOfBuildings[b] for 5 Int, exactly 5 Building, exactly 10 Room
    assert all b: Building | noRankingAboveNumberOfBuildings[b] is necessary for inventoryWellformed for 5 Int, exactly 5 Building, exactly 10 Room
    -- check no building rank ties
    assert all disj b1, b2: Building | inventoryWellformed is sufficient for noBuilingRankTies[b1, b2] for 5 Int, exactly 5 Building, exactly 10 Room
    assert all disj b1, b2: Building | noBuilingRankTies[b1, b2] is necessary for inventoryWellformed for 5 Int, exactly 5 Building, exactly 10 Room
    -- check room capacities are valid
    assert all r: Room | inventoryWellformed is sufficient for roomsHaveValidCapacities[r] for 5 Int, exactly 5 Building, exactly 10 Room
    assert all r: Room | roomsHaveValidCapacities[r] is necessary for inventoryWellformed for 5 Int, exactly 5 Building, exactly 10 Room
    -- check room ranks are valid
    assert all r: Room | inventoryWellformed is sufficient for roomsHaveValidRanks[r] for 5 Int, exactly 5 Building, exactly 10 Room
    assert all r: Room | roomsHaveValidRanks[r] is necessary for inventoryWellformed for 5 Int, exactly 5 Building, exactly 10 Room
    -- check no room rank ties
    assert all disj r1, r2: Room | inventoryWellformed is sufficient for noRoomRankTies[r1, r2] for 5 Int, exactly 5 Building, exactly 10 Room
    assert all disj r1, r2: Room | noRoomRankTies[r1, r2] is necessary for inventoryWellformed for 5 Int, exactly 5 Building, exactly 10 Room
    -- check rooms have different capacities
    assert some disj r1, r2: Room | {
        inventoryWellformed
        roomsHaveDifferentCapacities[r1, r2]
    } is sat for 5 Int, exactly 5 Building, exactly 10 Room
    -- check at least one room of each capacity exists
    assert some r1, r2, r3, r4, r5, r6: Room | {
        inventoryWellformed
        atLeastOneRoomOfEachCapacity[r1, r2, r3, r4, r5, r6]
    } is sat for 5 Int, exactly 5 Building, exactly 10 Room
    -- check building rank induces room rank order
    assert all disj r1, r2: Room | inventoryWellformed is sufficient for buildingRankInducesRoomRankOrder[r1, r2] for 5 Int, exactly 5 Building, exactly 10 Room
    assert all disj r1, r2: Room | buildingRankInducesRoomRankOrder[r1, r2] is necessary for inventoryWellformed for 5 Int, exactly 5 Building, exactly 10 Room
    -- example sat
    assert {
        inventoryWellformed
        some r1, r2: Room {
            r1.building.buildingRank = 1
            r2.building.buildingRank = 2
            r1.roomRank = 1
            r2.roomRank = 2
        }
    } is sat for 5 Int, exactly 5 Building, exactly 10 Room
    -- example unsat
    assert {
        inventoryWellformed
        some r: Room {
            -- violates room capacity constraints
            r.capacity = 7
        }
    } is unsat for 5 Int, exactly 5 Building, exactly 10 Room
    assert {
        inventoryWellformed
        some disj r1, r2: Room {
            -- violates building rank induces room rank order
            r1.building.buildingRank = 1
            r2.building.buildingRank = 2
            r1.roomRank = 2
            r2.roomRank = 1
        }
    } is unsat for 5 Int, exactly 5 Building, exactly 10 Room
}

pred noOverfilledRooms[r: Room] {
    # { s: Student | s.room = r } <= r.capacity
}

pred noRoomsSharedAcrossGroupsInFirstPass[s1, s2: Student, r: Room] {
    (s1.room = r and s2.room = r) implies s1.group = s2.group
}

test suite for assignmentWellformed {
    assert assignmentWellformed is sat for 5 Int, exactly 5 Building, exactly 10 Room, exactly 12 Student, exactly 4 Group
    -- check no room is overfilled
    assert all r: Room | assignmentWellformed is sufficient for noOverfilledRooms[r] for 5 Int, exactly 5 Building, exactly 10 Room, exactly 12 Student, exactly 4 Group
    assert all r: Room | noOverfilledRooms[r] is necessary for assignmentWellformed for 5 Int, exactly 5 Building, exactly 10 Room, exactly 12 Student, exactly 4 Group
    -- check rooms are not shared across groups in first pass
    assert all r: Room, s1, s2: Student | assignmentWellformed is sufficient for noRoomsSharedAcrossGroupsInFirstPass[s1, s2, r] for 5 Int, exactly 5 Building, exactly 10 Room, exactly 12 Student, exactly 4 Group
    assert all r: Room, s1, s2: Student | noRoomsSharedAcrossGroupsInFirstPass[s1, s2, r] is necessary for assignmentWellformed for 5 Int, exactly 5 Building, exactly 10 Room, exactly 12 Student, exactly 4 Group
    -- example sat
    assert {
        inventoryWellformed
        assignmentWellformed
        some r: Room {
            # { s: Student | s.room = r } = 2
        }
    } is sat for 5 Int, exactly 5 Building, exactly 10 Room, exactly 12 Student, exactly 4 Group
    -- example unsat
    assert {
        inventoryWellformed -- to ensure we have valid rooms capacity
        assignmentWellformed
        some r: Room {
            # { s: Student | s.room = r } = 7
        }
    } is unsat for 5 Int, exactly 5 Building, exactly 10 Room, exactly 12 Student, exactly 4 Group
}

pred group1StartsNoLaterThanGroup2[g1, g2: Group] {
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

test suite for groupStartsNoLaterThanLaterGroups {
    assert groupStartsNoLaterThanLaterGroups is sat for 5 Int, exactly 5 Building, exactly 10 Room, exactly 12 Student, exactly 4 Group
    -- check group 1 starts no later than group 2
    assert all disj g1, g2: Group | groupStartsNoLaterThanLaterGroups is sufficient for group1StartsNoLaterThanGroup2[g1, g2] for 5 Int, exactly 5 Building, exactly 10 Room, exactly 12 Student, exactly 4 Group
    assert all disj g1, g2: Group | group1StartsNoLaterThanGroup2[g1, g2] is necessary for groupStartsNoLaterThanLaterGroups for 5 Int, exactly 5 Building, exactly 10 Room, exactly 12 Student, exactly 4 Group
    -- example sat
    assert {
        lotteryBands
        groupsWellformed
        inventoryWellformed
        assignmentWellformed
        groupStartsNoLaterThanLaterGroups
        some g1, g2: Group {
            g1.pickNumber = 1
            g2.pickNumber = 2
            some s1: Student | s1.group = g1 and s1.room.roomRank = 1
            some s2: Student | s2.group = g2 and s2.room.roomRank = 2
        }
    } is sat for 5 Int, exactly 5 Building, exactly 10 Room, exactly 12 Student, exactly 4 Group
    -- example unsat
    assert {
        lotteryBands
        groupsWellformed
        inventoryWellformed
        assignmentWellformed
        groupStartsNoLaterThanLaterGroups
        some disj g1, g2: Group {
            g1.pickNumber = 1
            g2.pickNumber = 2
            some s1: Student | s1.group = g1 and s1.room.roomRank = 2
            some s2: Student | s2.group = g2 and s2.room.roomRank = 1
        }
    } is unsat for 5 Int, exactly 5 Building, exactly 10 Room, exactly 12 Student, exactly 4 Group
}
