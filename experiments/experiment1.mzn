int: start_semester;
int: no_of_grad_courses;

int: max_unit = 4;
int: max_load = 4;
int: no_of_semesters = 4;
int: prereq_dim0 = 3;
int: prereq_dim1 = 3;
int: coreq_dim = 1;
int: coreq_dim0 = 1;
int: incompat_dim0 = 1;
int: incompat_dim1 = 3;

enum courses;
enum semesters = {odd_first, odd_second, even_first, even_second};
set of int: units = 1 .. max_unit;
set of int: all_semesters = 0 .. no_of_semesters;
set of courses: grad_courses;
set of courses: undergrad_courses;
array[courses] of var all_semesters: takes;
array[grad_courses] of set of semesters: offered_semester;
array[grad_courses] of set of int: time_unit_available;
array[grad_courses] of var units: time_unit;

array[1..no_of_grad_courses * prereq_dim0 * prereq_dim1] of courses: prereq;
array[1..no_of_grad_courses, 1..prereq_dim0, 1..prereq_dim1] of courses: prerequisite = array3d(1..no_of_grad_courses, 1..prereq_dim0, 1..prereq_dim1, prereq);
array[1..no_of_grad_courses * coreq_dim0] of courses: corequisite;
array[1..no_of_grad_courses * incompat_dim0 * incompat_dim1] of courses: incompat;
array[1..no_of_grad_courses, 1..incompat_dim0, 1..incompat_dim1] of courses: incompatible = array3d(1..no_of_grad_courses, 1..incompat_dim0, 1..incompat_dim1, incompat);

array[grad_courses] of int: preference;

array[1..6] of courses: list2;
array[1..2] of courses: list3;
array[1..2] of courses: list4;
array[1..2] of courses: list5;
array[1..3] of courses: list6;
array[1..37] of courses: list7;
array[1..37] of courses: list8;
array[1..4] of courses: list10;
array[1..3] of courses: list12;
array[1..5] of courses: list13;
array[1..3] of courses: list15;
array[1..7] of courses: list16;


array[1..29] of courses: level8;
% Signal may be 1, 0, or -1. signal = 0 means that total number of units is larger than req_unit, and signal = 1 / -1 means larger than / smaller than correspondingly.
predicate requirement_node(array[int] of var int: takes, array[int] of courses: requirement, int: signal, int: req_unit) =
            ((signal != 0 -> (sum(c in requirement where takes[c] != 0)(time_unit[c]) * signal) >= req_unit * signal)
             /\ (signal = 0 -> sum(c in requirement where takes[c] != 0)(time_unit[c]) = req_unit));
         
predicate prerequisite_criteria(courses: c1, courses: c2, array[int] of var int: takes) = 
            (takes[c1] < takes[c2] /\ takes[c1] != 0);

predicate corequisite_criteria(courses: c1, courses: c2, array[int] of var int: takes) = 
            (takes[c1] <= takes[c2] /\ takes[c1] != 0);

predicate level_criteria(array[int] of var int: takes, set of courses: list1, array[int] of courses: level8, int: req_unit) =
            (sum(c in (array2set(level8) intersect list1) where takes[c] != 0)(time_unit[c]) >= req_unit);

% Calculate sum of units of input list.     
function var int: unit_sum(array[int] of courses: requirement) = (sum(c in requirement where takes[c] != 0)(time_unit[c]));

constraint forall(c in grad_courses)
            (time_unit[c] in time_unit_available[c]);

constraint forall(i in 1..no_of_grad_courses)
            ((takes[to_enum(courses, i)] != 0)
            -> (forall(j in 1..prereq_dim0)
                (exists(k in 1..prereq_dim1)(prerequisite[i, j, k] != to_enum(courses, no_of_grad_courses+1))
                 -> (exists(k in 1..3 where prerequisite[i, j, k] != to_enum(courses, no_of_grad_courses+1))
                     (prerequisite_criteria(prerequisite[i, j, k], to_enum(courses, i), takes))))));
              
constraint forall(i in 1..no_of_grad_courses)
            ((takes[to_enum(courses, i)] != 0)
            -> ((corequisite[i] == to_enum(courses, no_of_grad_courses+1)) \/ (corequisite_criteria(corequisite[i], to_enum(courses, i), takes))));

constraint forall(i in 1..no_of_grad_courses)
            ((takes[to_enum(courses, i)] != 0)
            -> (forall(j in 1..incompat_dim0, k in 1..incompat_dim1)
                (incompatible[i, j, k] == to_enum(courses, no_of_grad_courses+1) \/ takes[incompatible[i, j, k]] = 0)));
                
% Restrict that no one can take a course when the course is not offered.
constraint forall(c in grad_courses)
            ((takes[c] = 0) \/ (to_enum(semesters, (((start_semester - 1 + takes[c]) - 1) mod no_of_semesters) + 1) in offered_semester[c]));

% Restrict that no undergrad courses (courses in prereq/coreq/incompat which does not belong to the requirement tree) could be taken.
constraint forall(c in undergrad_courses)
            (takes[c] = 0);

% Sum of load is 4.
constraint forall(s in 1..no_of_semesters)
            (sum(c in grad_courses where takes[c] == s)(time_unit[c]) = max_load);

% Preference is 5 means a hard preference of taking this course, 0 means a hard preference of not taking it.
constraint :: "HardPreference"
            forall(c in grad_courses)
            ((preference[c] == 5 -> takes[c] != 0) /\ (preference[c] == 0 -> takes[c] == 0));

constraint ( unit_sum(list2) + unit_sum(list3) + unit_sum(list4) + unit_sum(list5) + unit_sum(list6) + unit_sum(list7) + unit_sum(list8) + unit_sum(list10) + unit_sum(list12) + unit_sum(list13) + unit_sum(list15) + unit_sum(list16) >= 16 /\ level_criteria(takes, (array2set(list2) union array2set(list3) union array2set(list4) union array2set(list5) union array2set(list6) union array2set(list7) union array2set(list8) union array2set(list10) union array2set(list12) union array2set(list13) union array2set(list15) union array2set(list16)), level8, 6) /\ requirement_node(takes, list2, 0, 6) /\ requirement_node(takes, list3, 0, 1) /\ requirement_node(takes, list4, 0, 1) /\ requirement_node(takes, list5, 0, 1) /\ requirement_node(takes, list6, 0, 2) /\ ( ( requirement_node(takes, list7, 0, 5) ) \/ ( requirement_node(takes, list8, 0, 1) /\ ( ( unit_sum(list10) >= 4 /\ requirement_node(takes, list10, 0, 4) ) \/ ( unit_sum(list12) + unit_sum(list13) >= 4 /\ requirement_node(takes, list12, 0, 3) /\ requirement_node(takes, list13, 0, 1) ) \/ ( unit_sum(list15) + unit_sum(list16) >= 4 /\ level_criteria(takes, (array2set(list15) union array2set(list16)), level8, 2) /\ requirement_node(takes, list15, -1, 2) /\ requirement_node(takes, list16, 1, 2) ) ) ) )  ) ;

solve maximize sum(c in grad_courses where takes[c] != 0)(preference[c]);

output["1 "];
output[show(c) ++ " "| c in grad_courses where fix(takes[c]) = 1];
output["2 "];
output[show(c) ++ " "| c in grad_courses where fix(takes[c]) = 2];
output["3 "];
output[show(c) ++ " "| c in grad_courses where fix(takes[c]) = 3];
output["4 "];
output[show(c) ++ " "| c in grad_courses where fix(takes[c]) = 4];
