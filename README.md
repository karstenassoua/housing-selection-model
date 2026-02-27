# housing-selection-model
what it says on the tin. please give us an A tim


## Project Objective
#### What are you trying to model? Include a brief description that would give someone unfamiliar with the topic a basic understanding of your goal.

Every academic year rising sophomores, juniors, and seniors at Brown University enter a housing lottery to determine which campus residence they will have the privilege (or misfortune) of living in next year.

Students may approach the process alone or form a group. Regardless of group membership, all students in the housing lottery are randomly assigned housing lottery time slots. During these slots they are able to select rooms that exactly matches their group size in campus residences.

Necessarily, every student who is a member of the lottery must eventually be assigned to a room.

## Model Design and Visualization
#### Give an overview of your model design choices, what checks or run statements you wrote, and what we should expect to see from an instance produced by the Sterling visualizer. How should we look at and interpret an instance created by your spec? Did you create a custom visualization, or did you use the default?

- We are excluding freshmen, transfers and all of their dormitories, as they do not enter the housing lottery.
- Not all seniors and juniors participate in the housing lottery. As such it is possible for one to be both a Senior and all have no Housing number. However if one does not have a Housing number, they do not exist and are NOTHING to us!

## Signatures and Predicates
#### At a high level, what do each of your sigs and preds represent in the context of the model? Justify the purpose for their existence and how they fit together.

## Testing
#### What tests did you write to test your model itself? What tests did you write to verify properties about your domain area? Feel free to give a high-level overview of this.

Firstly in each test, we made sure to include satisfiability checks for each of the main predicates utilized in the housing lottery. This ensures that the model isn't accidentally overconstrained from its predicates and that all of them can actually be satisfied in some world. In addition, we added sufficiency and necessity checks for each predicate, checking that for sub-constraints of a main predicate, that if the main predicate is true, then the sub-property must also be true (sufficiency) and if we remove that sub-property, the main predicate should no longer be guaranteed (necessity). This can be shown in all of the test predicates we created (like SeniorBands, allStudentsInGroups, etc.). Finally, we made sure to include examples of sat and unsat scenarios for each of the constraints, where we have one example that will clearly pass and only thatviolates at least one of the sub predicates directly. Most of the tests are fit for 5 Int, 5 Buildings, 10 Rooms, 12 Students, etc. for quick runtimes, but the overall model can work with a variety of different student/room/building/group numbers. These tests overall ensure that the model works correctly and sufficiently satistifies its baseline conditions.

## Documentation
#### Make sure your model and test files are well-documented. This will help in understanding the structure and logic of your project.