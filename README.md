# housing-selection-model
what it says on the tin. please give us an A tim


## Project Objective
#### What are you trying to model? Include a brief description that would give someone unfamiliar with the topic a basic understanding of your goal.

Every academic year rising sophomores, juniors, and seniors at Brown University enter a housing lottery to determine which campus residence they will have the privilege (or misfortune) of living in next year. Students may approach the process alone or form a group. Regardless of group membership, all students in the housing lottery are randomly assigned housing lottery time slots. During these slots they are able to select rooms that exactly matches their group size in campus residences. Necessarily, every student who is a member of the lottery must eventually be assigned to a room.

Our model intends to formalize the housing lottery process in Forge, representing students, housing groups, buildings, and rooms, along with the structural and fairness rules that exist for housing assignments. This model includes important constraints of a housing lottery, such as lottery number bands by class year, maximum group sizes, room capacity limits, and the requirement that earlier lottery picks will tend to pick better dorms compared to later ones. Ultimately, we want to show that every student in the lottery is assigned to exactly one room while respecting capacity, ordering, and grouping rules that exist in the current Reslife system.

## Model Design and Visualization
#### Give an overview of your model design choices, what checks or run statements you wrote, and what we should expect to see from an instance produced by the Sterling visualizer. How should we look at and interpret an instance created by your spec? Did you create a custom visualization, or did you use the default?

- We are excluding freshmen, transfers and all of their dormitories, as they do not enter the housing lottery.
- Not all seniors and juniors participate in the housing lottery. As such it is possible for one to be both a Senior and all have no Housing number. However if one does not have a Housing number, they do not exist and are NOTHING to us!

## Signatures and Predicates
#### At a high level, what do each of your sigs and preds represent in the context of the model? Justify the purpose for their existence and how they fit together.

Sigs:
- Year (Senior, Junior, Sophomore extend Year): This represents the class-year category of a student (rising senior/junior/sophomore). This is necessary because each class year has its own allowed lottery-number range, where older years are supposed to get better lottery placements. Student.year points to one of these, and lotteryBands uses Year to constrain Student.lotteryNumber.
- Group: This represents how in the Brown lottery system, you can join a housing group that (usually) picks together as a unit. This is necessary as the lottery operates on group time slots, where the pickNumber is the group's position in the lottery order (earlier pick means earlier housing choice). Student.group assigns each student to exactly one group, and the groupsWellforward predicate is meant to link each student's lotteryNumber to the group's pickNumber.
- Student: This represents an individual student in the housing lottery process. A student's background matters in the context of the lottery, as their class year drives their lottery band, lotteryNumber determines their lottery outcome, their group captures their picking unit, and room represents their outcome of the housing lottery. Student is used in nearly every predicate through constraining something about students, such as what are valid lottery numbers, group membership, room assignments, and group-consistency within rooms.
- Building: This represents a dorm building on campus containing rooms that are open. These building are ordered by desirability/priority, representing specific majority dorm preferences of students. This exists because the model itself needs a specific selection logic, determining preferences for students and sturcturing the inventory of dorms. This fits with Room.building linking each room to a building, and the predicate inventoryWellformed ensures ranks are valid and unique and that building order informs room order.
- Room: This represents an individual housing dorm available in the lottery, with a specific size limit and position in the global ordering of available rooms. It exists as the crux of the model, where students select specific rooms that they would like to live in for the next year. The predicate of assignmentWellformed constrains how students occupy rooms, while the predicate of inventoryWellformed constrains capacities and rankings across buildings.
Predicates:
- lotteryBands: enforces the lottery numbers that are assigned to a specific class year. This ensures the inputs to the lottery are realistic (a senior picks before a sophomore).
- groupsWellformed: ensures no empty groups and max group size 6, every student's lotteryNumber equals their group's pickNumber, and all groups have a distinct pickNumber. This is important as this makes groups act as real lottery units and avoids ambiguous ordering.
- inventoryWellformed: this defines a consistent inventory for the lottery, ensuring that building ranks are in range and unique, room caps range from 1 to 6, roomRank is positive and unique globally, there is at least one room of each cap, and finally all rooms in earlier buildings have earlier roomRanks. The purpose is that this prevents any illogical housing lottery patterns (rooms are identical, bizarre rankings).
- assignmentWellformed: This constrains what counts as a valid assignment outcome by ensuring no room is over capacity and a room cannot mix multiple groups (everyone in the same room must share the same group). This is important as we need to ensure the allocated assignments do not violate room caps and matches the assumption that groups do not split (unless there are no valid options for the group).
- groupStartsNoLaterThanLaterGroups: This ensures the following condition that if group 1 has an earlier pickNumber than group 2, then the earliest room used by group 1 must be no later than the earliest room used by group 2. This is meant to enforce the idea that earlier pick groups shouldn't be forced to start selection after later pick groups.
- firstPassHousingLottery: This predicate combines all of the previous predicates, simulating a full pass through the housing lottery. This is the central predicate to the housing lottery model we are trying to demonstrate.

These sigs define the important players of the housing lottery, while the predicates constraint them to realistically demonstrate a true housing lottery process. Overall, they aim to give possible lottery and assignment outcomes that are consistent with an actual housing lottery process from Reslife.

## Testing
#### What tests did you write to test your model itself? What tests did you write to verify properties about your domain area? Feel free to give a high-level overview of this.

Firstly in each test, we made sure to include satisfiability checks for each of the main predicates utilized in the housing lottery. This ensures that the model isn't accidentally overconstrained from its predicates and that all of them can actually be satisfied in some world. In addition, we added sufficiency and necessity checks for each predicate, checking that for sub-constraints of a main predicate, that if the main predicate is true, then the sub-property must also be true (sufficiency) and if we remove that sub-property, the main predicate should no longer be guaranteed (necessity). This can be shown in all of the test predicates we created (like SeniorBands, allStudentsInGroups, etc.). Finally, we made sure to include examples of sat and unsat scenarios for each of the constraints, where we have one example that will clearly pass and only thatviolates at least one of the sub predicates directly. Most of the tests are fit for 5 Int, 5 Buildings, 10 Rooms, 12 Students, etc. for quick runtimes, but the overall model can work with a variety of different student/room/building/group numbers. These tests overall ensure that the model works correctly and sufficiently satistifies its baseline conditions.

## Documentation
#### Make sure your model and test files are well-documented. This will help in understanding the structure and logic of your project.

Comments in both the model and the test suite are clearly documented. The predicates in the main file clear document the purpose of each of the sub-constraints, while the predicates in the testing file clearly name the sub-constraints they are testing for.