include "general.mzn";

array[grad_courses] of -1..4: old_plan;

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

constraint (unit_sum(list2) + unit_sum(list3) + unit_sum(list4) + unit_sum(list5) + unit_sum(list6) + unit_sum(list7) + unit_sum(list8) + unit_sum(list10) + unit_sum(list12) + unit_sum(list13) + unit_sum(list15) + unit_sum(list16) >= 16);

constraint ( unit_sum(list2) + unit_sum(list3) + unit_sum(list4) + unit_sum(list5) + unit_sum(list6) + unit_sum(list7) + unit_sum(list8) + unit_sum(list10) + unit_sum(list12) + unit_sum(list13) + unit_sum(list15) + unit_sum(list16) >= 16 /\ level_criteria(takes, (array2set(list2) union array2set(list3) union array2set(list4) union array2set(list5) union array2set(list6) union array2set(list7) union array2set(list8) union array2set(list10) union array2set(list12) union array2set(list13) union array2set(list15) union array2set(list16)), level8, 6) /\ requirement_node(takes, list2, 0, 6) /\ requirement_node(takes, list3, 0, 1) /\ requirement_node(takes, list4, 0, 1) /\ requirement_node(takes, list5, 0, 1) /\ requirement_node(takes, list6, 0, 2) /\ ( ( requirement_node(takes, list7, 0, 5) ) \/ ( requirement_node(takes, list8, 0, 1) /\ ( ( unit_sum(list10) >= 4 /\ requirement_node(takes, list10, 0, 4) ) \/ ( unit_sum(list12) + unit_sum(list13) >= 4 /\ requirement_node(takes, list12, 0, 3) /\ requirement_node(takes, list13, 0, 1) ) \/ ( unit_sum(list15) + unit_sum(list16) >= 4 /\ level_criteria(takes, (array2set(list15) union array2set(list16)), level8, 2) /\ requirement_node(takes, list15, -1, 2) /\ requirement_node(takes, list16, 1, 2) ) ) ) )  ) ;

solve minimize sum(c in grad_courses where old_plan[c] > 0)(abs(old_plan[c]-takes[c])) + sum(c in grad_courses where old_plan[c] == -1)(abs(takes[c]));