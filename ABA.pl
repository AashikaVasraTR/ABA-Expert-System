%%%%%%%%%% Rule Based Expert System Shell %%%%%%%%%%
%%%
%%% This is the expert system with the example from the textbook:
%%%
%%% Artificial Intelligence:
%%% Structures and strategies for complex problem solving
%%%
%%% by George F. Luger and William A. Stubblefield
%%%
%%% These programs are copyrighted by Benjamin//Cummings Publishers.
%%%
%%% Modified by Shaun-inn Wu
%%%
%%% These program are offered for educational purposes only.
%%%
%%% Disclaimer: These programs are provided with no warranty whatsoever as to
%%% their correctness, reliability, or any other property.  We have written
%%% them for specific educational purposes, and have made no effort
%%% to produce commercial quality computer programs.  Please do not expect
%%% more of them then we have intended.
%%%
%%% This code has been tested with SWI-Prolog (Multi-threaded, Version 7.6.4)
%%% and appears to function as intended.


% solve(Goal): solve(fix_car(Advice)) for the car problem.
% Top level call.  Initializes working memory; attempts to solve Goal
% with certainty factor; prints results; asks user if they would like a
% trace.

solve(Goal) :-
    init, print_help,
    solve(Goal,C,[],1),
    nl,write('Solved '),write(Goal),
    write(' With Certainty = '),write(C),nl,nl,
    ask_for_trace(Goal).

% init
% purges all facts from working memory.

init :- retractm(fact(X)), retractm(untrue(X)).

% solve(Goal,CF,Rulestack,Cutoff_context)
% Attempts to solve Goal by backwards chaining on rules;  CF is
% certainty factor of final conclusion; Rulestack is stack of
% rules, used in why queries, Cutoff_context is either 1 or -1
% depending on whether goal is to be proved true or false
% (e.g. not Goal requires Goal be false in oreder to succeed).

solve(true,100,Rules,_).

solve(A,100,Rules,_) :-
    fact(A).

solve(A,-100,Rules,_) :-
    untrue(A).

solve(not(A),C,Rules,T) :-
    T2 is -1 * T,
    solve(A,C1,Rules,T2),
    C is -1 * C1.

solve((A,B),C,Rules,T) :-
    solve(A,C1,Rules,T),
    above_threshold(C1,T),
    solve(B,C2,Rules,T),
    above_threshold(C2,T),
    minimum(C1,C2,C).

solve(A,C,Rules,T) :-
    rule((A :- B),C1),
    solve(B,C2,[rule(A,B,C1)|Rules],T),
    C is (C1 * C2) / 100,
    above_threshold(C,T).

solve(A,C,Rules,T) :-
    rule((A), C),
    above_threshold(C,T).

solve(A,C,Rules,T) :-
    askable(A),
    not(known(A)),
    ask(A,Answer),
    respond(Answer,A,C,Rules).

% respond( Answer, Query, CF, Rule_stack).
% respond will process Answer (yes, no, how, why, help).
% asserting to working memory (yes or no)
% displaying current rule from rulestack (why)
% showing proof trace of a goal (how(Goal)
% displaying help (help).
% Invalid responses are detected and the query is repeated.

respond(Bad_answer,A,C,Rules) :-
    not(member(Bad_answer,[help, yes,no,why,how(_)])),
    write('answer must be either help, (y)es, (n)o, (h)ow(X), (w)hy'),nl,nl,
    ask(A,Answer),
    respond(Answer,A,C,Rules).

respond(yes,A,100,_) :-
    assert(fact(A)).

respond(no,A,-100,_) :-
    assert(untrue(A)).

respond(why,A,C,[Rule|Rules]) :-
    display_rule(Rule),
    ask(A,Answer),
    respond(Answer,A,C,Rules).

respond(why,A,C,[]) :-
    write('Back to goal, no more explanation  possible'),nl,nl,
    ask(A,Answer),
    respond(Answer,A,C,[]).

respond(how(Goal),A,C,Rules) :-
    respond_how(Goal),
    ask(A,Answer),
    respond(Answer,A,C,Rules).

respond(help,A,C,Rules) :-
    print_help,
    ask(A,Answer),
    respond(Answer,A,C,Rules).

% ask(Query, Answer)
% Writes Query and reads the Answer.  Abbreviations (y, n, h, w) are
% trnslated to appropriate command be filter_abbreviations

ask(Query,Answer) :-
    display_query(Query),
    read(A),
    filter_abbreviations(A,Answer),!.

% filter_abbreviations( Answer, Command)
% filter_abbreviations will expand Answer into Command.  If
% Answer is not a known abbreviation, then Command = Answer.

filter_abbreviations(y,yes).
filter_abbreviations(n,no).
filter_abbreviations(w,why).
filter_abbreviations(h,help).
filter_abbreviations(h(X),how(X)).
filter_abbreviations(X,X).

% known(Goal)
% Succeeds if Goal is known to be either true or untrue.

known(Goal) :- fact(Goal).
known(Goal) :- untrue(Goal).

% ask_for_trace(Goal).
% Invoked at the end of a consultation, ask_for_trace asks the user if
% they would like a trace of the reasoning to a goal.

ask_for_trace(Goal) :-
    write('Trace of reasoning to goal ? '),
    read(Answer),nl,
    show_trace(Answer,Goal),!.

% show_trace(Answer,Goal)
% If Answer is ``yes'' or ``y,'' show trace will display  a trace
% of Goal, as in a ``how'' query.  Otherwise, it succeeds, doing nothing.

show_trace(yes,Goal) :- respond_how(Goal).

show_trace(y,Goal) :- respond_how(Goal).

show_trace(_,_).

% print_help
% Prints a help screen.

print_help :-
    write('Exshell allows the following responses to queries:'),nl,nl,
    write('   yes - query is known to be true.'),nl,
    write('   no - query is false.'),nl,
    write('   why - displays rule currently under consideration.'),nl,
    write('   how(X) - if X has been inferred, displays trace of reasoning.'),nl,
    write('   help - prints this message.'),nl,
    write('   Your response may be abbreviated to the first letter and must end with a period (.).'),nl.

% display_query(Goal)
% Shows Goal to user in the form of a query.

display_query(Goal) :-
    write(Goal),
    write('? ').

% display_rule(rule(Head, Premise, CF))
% prints rule in IF...THEN form.

display_rule(rule(Head,Premise,CF)) :-
    write('IF       '),
    write_conjunction(Premise),
    write('THEN     '),
    write(Head),nl,
    write('CF   '),write(CF),
    nl,nl.

% write_conjunction(A)
% write_conjunction will print the components of a rule premise.  If any
% are known to be true, they are so marked.

write_conjunction((A,B)) :-
    write(A), flag_if_known(A),!, nl,
    write('     AND '),
    write_conjunction(B).

write_conjunction(A) :- write(A),flag_if_known(A),!, nl.

% flag_if_known(Goal).
% Called by write_conjunction, if Goal follows from current state
% of working memory, prints an indication, with CF.

flag_if_known(Goal) :-
    build_proof(Goal,C,_,1),
    write('     ***Known, Certainty = '),write(C).

flag_if_known(A).

% Predicates concerned with how queries.

% respond_how(Goal).
% calls build_proof to determine if goal follows from current state of working
% memory.  If it does, prints a trace of reasoning, if not, so indicates.

respond_how(Goal) :-
    build_proof(Goal,C,Proof,1),
    interpret(Proof),nl,!.

respond_how(Goal) :-
    build_proof(Goal,C,Proof,-1),
    interpret(Proof),nl,!.

respond_how(Goal) :-
    write('Goal does not follow at this stage of consultation.'),nl.

% build_proof(Goal, CF, Proof, Cutoff_context).
% Attempts to prove Goal, placing a trace of the proof in Proof.
% Functins the same as solve, except it does not ask for unknown information.
% Thus, it only proves goals that follow from the rule base and the current
% contents of working memory.

build_proof(true,100,(true,100),_).

build_proof(Goal, 100, (Goal :- given,100),_) :- fact(Goal).

build_proof(Goal, -100, (Goal :- given,-100),_) :- untrue(Goal).

build_proof(not(Goal), C, (not(Proof),C),T) :-
    T2 is -1 * T,
    build_proof(Goal,C1,Proof,T2),
    C is -1 * C1.

build_proof((A,B),C,(ProofA, ProofB),T) :-
    build_proof(A,C1,ProofA,T),
    above_threshold(C1,T),
    build_proof(B,C2,ProofB,T),
    above_threshold(C2,T),
    minimum(C1,C2,C).

build_proof(A, C, (A :- Proof,C),T) :-
    rule((A :- B),C1),
    build_proof(B, C2, Proof,T),
    C is (C1 * C2) / 100,
    above_threshold(C,T).

build_proof(A, C, (A :- true,C),T) :-
    rule((A),C),
    above_threshold(C,T).

% interpret(Proof).
% Interprets a Proof as constructed by build_proof,
% printing a trace for the user.

interpret((Proof1,Proof2)) :-
    interpret(Proof1),interpret(Proof2).

interpret((Goal :- given,C)):-
    write(Goal),
    write(' was given. CF = '), write(C),nl,nl.

interpret((not(Proof), C)) :-
    extract_body(Proof,Goal),
    write('not '),
    write(Goal),
    write(' CF = '), write(C),nl,nl,
    interpret(Proof).

interpret((Goal :- true,C)) :-
    write(Goal),
        write(' is a fact, CF = '),write(C),nl.

interpret(Proof) :-
    is_rule(Proof,Head,Body,Proof1,C),
    nl,write(Head),write(' CF = '),
    write(C), nl,write('was proved using the rule'),nl,nl,
    rule((Head :- Body),CF),
    display_rule(rule(Head, Body,CF)), nl,
    interpret(Proof1).

% isrule(Proof,Goal,Body,Proof,CF)
% If Proof is of the form Goal :- Proof, extracts
% rule Body from Proof.

is_rule((Goal :- Proof,C),Goal, Body, Proof,C) :-
    not(member(Proof, [true,given])),
    extract_body(Proof,Body).

% extract_body(Proof).
% extracts the body of the top level rule from Proof.

extract_body((not(Proof), C), (not(Body))) :-
    extract_body(Proof,Body).

extract_body((Proof1,Proof2),(Body1,Body2)) :-
    !,extract_body(Proof1,Body1),
    extract_body(Proof2,Body2).

extract_body((Goal :- Proof,C),Goal).

% Utility Predicates.

retractm(X) :- retract(X), fail.
retractm(X) :- retract((X:-Y)), fail.
retractm(X).

member(X,[X|_]).
member(X,[_|T]) :- member(X,T).

minimum(X,Y,X) :- X =< Y.
minimum(X,Y,Y) :- Y < X.

above_threshold(X,1) :- X >= 20.
above_threshold(X,-1) :- X =< -20.


%%%
%%% The following is the knowledge base for ABA behavior classification and reward status:
%%%

% Top level goal, starts search.
rule((therapy(Advice) :-
	function_of_behavior(Y), fix(Y,Advice)),100).

% rules to infer major classifications of ABA behaviors
% 5 major classes - Attention seeking, Access to Tangibles, Self regulatory, Escape/Avoidance  %			and normal behavior
% Reward status is added to all steps to ensure if the existing reward works or not.
% Reward status is a completely different function and doesn’t play role in classification.

rule((function_of_behavior(normal_behavior) :- bad_behavior(acceptable)), 100).

rule((function_of_behavior(access_to_tangibles_objects_new_reward):- bad_behavior(not(acceptable)), receive_object, not(negative_trend_in_calming_time_with_current_reward)), 90).
rule((function_of_behavior(access_to_tangibles_objects_same_reward):- bad_behavior(not(acceptable)), receive_object,negative_trend_in_calming_time_with_current_reward), 90).

rule((function_of_behavior(access_to_tangibles_activity_new_reward):- bad_behavior(not(acceptable)), receive_activity, not(negative_trend_in_calming_time_with_current_reward)), 90).
rule((function_of_behavior(access_to_tangibles_activity_same_reward):- bad_behavior(not(acceptable)), receive_activity, negative_trend_in_calming_time_with_current_reward), 90).

rule((function_of_behavior(escape_avoidance_run_away_new_reward):- bad_behavior(not(acceptable)), caused_trouble_after_some_event_occurance, stopped_after_moved_away_from_event, not(negative_trend_in_calming_time_with_current_reward)), 80).
rule((function_of_behavior(escape_avoidance_run_away_same_reward):- bad_behavior(not(acceptable)), caused_trouble_after_some_event_occurance, stopped_after_moved_away_from_event,negative_trend_in_calming_time_with_current_reward), 80).

rule((function_of_behavior(escape_avoidance_destructive_new_reward):- bad_behavior(not(acceptable)), caused_trouble_after_some_event_occurance, destroyed_event_source, not(negative_trend_in_calming_time_with_current_reward)), 95).
rule((function_of_behavior(escape_avoidance_destructive_same_reward):- bad_behavior(not(acceptable)), caused_trouble_after_some_event_occurance, destroyed_event_source,negative_trend_in_calming_time_with_current_reward), 95).

rule((function_of_behavior(escape_avoidance_postpone_new_reward):- bad_behavior(not(acceptable)), caused_trouble_after_some_event_occurance, delayed_after_moved_away_from_event, not(negative_trend_in_calming_time_with_current_reward)), 95).
rule((function_of_behavior(escape_avoidance_postpone_same_reward):- bad_behavior(not(acceptable)), caused_trouble_after_some_event_occurance, delayed_after_moved_away_from_event,negative_trend_in_calming_time_with_current_reward), 95).

rule((function_of_behavior(attention_seeking_positive_new_reward):- bad_behavior(not(acceptable)), looks_at_other_people, calms_down_when_comforted, not(negative_trend_in_calming_time_with_current_reward)),95).
rule((function_of_behavior(attention_seeking_positive_same_reward):- bad_behavior(not(acceptable)), looks_at_other_people, calms_down_when_comforted,negative_trend_in_calming_time_with_current_reward),95).

rule((function_of_behavior(attention_seeking_negative_new_reward):- bad_behavior(not(acceptable)), looks_at_other_people,not(calms_down_when_comforted), not(negative_trend_in_calming_time_with_current_reward)), 90).
rule((function_of_behavior(attention_seeking_negative_same_reward):- bad_behavior(not(acceptable)), looks_at_other_people,not(calms_down_when_comforted),negative_trend_in_calming_time_with_current_reward), 90).

rule((function_of_behavior(self_regulatory_calming_new_reward):- bad_behavior(not(acceptable)), not(physically_harm_themselves),not(physically_harm_others_or_things), not(caused_trouble_after_some_event_occurance), not(stopped_after_moved_away_from_event), not(receive_object), not(receive_activity), not(negative_trend_in_calming_time_with_current_reward)), 80).
rule((function_of_behavior(self_regulatory_calming_same_reward):- bad_behavior(not(acceptable)), not(physically_harm_themselves), not(physically_harm_others_or_things), not(caused_trouble_after_some_event_occurance), not(stopped_after_moved_away_from_event), not(receive_object), not(receive_activity),negative_trend_in_calming_time_with_current_reward ), 80).
rule((function_of_behavior(self_regulatory_calming_new_reward):- bad_behavior(not(acceptable)), not(physically_harm_themselves), not(physically_harm_others_or_things), not(receive_object), not(receive_activity) , not(caused_trouble_after_some_event_occurance), not(looks_at_other_people), not(physically_harm_others_or_things), not(physically_harm_themselves), not(stopped_after_moved_away_from_event, negative_trend_in_calming_time_with_current_reward )), 80).
rule((function_of_behavior(self_regulatory_calming_same_reward):- bad_behavior(not(acceptable)), not(physically_harm_themselves), not(physically_harm_others_or_things), not(receive_object), not(receive_activity) , not(caused_trouble_after_some_event_occurance), not(looks_at_other_people), not(physically_harm_others_or_things), not(physically_harm_themselves), stopped_after_moved_away_from_event, negative_trend_in_calming_time_with_current_reward ), 80).

rule((function_of_behavior(self_regulatory_self_harm_new_reward):- bad_behavior(not(acceptable)), physically_harm_themselves, not(physically_harm_others_or_things), not(caused_trouble_after_some_event_occurance), not(stopped_after_moved_away_from_event), not(receive_object), not(receive_activity), not(negative_trend_in_calming_time_with_current_reward )), 70).
rule((function_of_behavior(self_regulatory_self_harm_same_reward):- bad_behavior(not(acceptable)), physically_harm_themselves, not(physically_harm_others_or_things), not(caused_trouble_after_some_event_occurance), not(stopped_after_moved_away_from_event), not(receive_object), not(receive_activity),negative_trend_in_calming_time_with_current_reward ), 70).


 

% Rules to infer bad behavior acceptability.
rule((bad_behavior(acceptable) :-not(socially_invalid), not(physically_harmful)),100).
rule((bad_behavior(not(acceptable)) :-socially_invalid, not(physically_harmful)),100).
rule((bad_behavior(not(acceptable)) :- physically_harmful,not(socially_invalid)),100).
rule((bad_behavior(not(acceptable)) :- physically_harmful,socially_invalid),100).

% Rules to print the observed classification and the reward status

rule(fix(normal_behavior, 'No therapy needed'),100).

rule(fix(access_to_tangibles_objects_new_reward, 'Function of Behavior: Access to Tangible object and Reward status : Insufficient.  Consult a therapist to determine a new reward'), 90).
rule(fix(access_to_tangibles_objects_same_reward, 'Function of Behavior: Access to Tangible object and Reward status : Sufficient.  Continue with same reward'), 90).

rule(fix(access_to_tangibles_activity_new_reward, 'Function of Behavior: Access to tangible activity and Reward status : Insufficient.  Consult a therapist to determine a new reward'), 90).
rule(fix(access_to_tangibles_activity_same_reward, 'Function of Behavior: Access to tangible activity and Reward status : Sufficient.  Continue with same reward'), 90).

rule(fix(escape_avoidance_run_away_new_reward, 'Function of Behavior : Run away category under Escape/Avoidance and Reward status : Insufficient.  Consult a therapist to determine a new reward'),95).
rule(fix(escape_avoidance_run_away_same_reward, 'Function of Behavior : Run away category under Escape/Avoidance and Reward status : Sufficient.  Continue with same reward'),95).

rule(fix(escape_avoidance_destructive_new_reward, 'Function of Behavior : Destructive category under Escape/Avoidance and Reward status : Insufficient.  Consult a therapist to determine a new reward'),95).
rule(fix(escape_avoidance_destructive_same_reward, 'Function of Behavior : Destructive category under Escape/Avoidance and Reward status : Sufficient.  Continue with same reward'),95).

rule(fix(escape_avoidance_postpone_new_reward, 'Function of Behavior : Postpone category under Escape/Avoidance and Reward status : Insufficient.  Consult a therapist to determine a new reward'),95).
rule(fix(escape_avoidance_postpone_same_reward, 'Function of Behavior : Postpone category under Escape/Avoidance and Reward status : Sufficient.  Continue with same reward'),95).

rule(fix(attention_seeking_positive_new_reward,'Function of Behavior : Positive Attention Seeking and Reward status : Insufficient.  Consult a therapist to determine a new reward'), 100).
rule(fix(attention_seeking_positive_same_reward,'Function of Behavior : Positive Attention Seeking and Reward status : Sufficient.  Continue with same reward'), 100).

rule(fix(attention_seeking_negative_new_reward,'Function of Behavior : Negative Attention Seeking and Reward status : Insufficient.  Consult a therapist to determine a new reward'), 100).
rule(fix(attention_seeking_negative_same_reward,'Function of Behavior : Negative Attention Seeking and Reward status : Sufficient.  Continue with same reward'), 100).

rule(fix(self_regulatory_calming_new_reward, 'Function of Behavior : Calming category under Self Regulatory and Reward status : Insufficient.  Consult a therapist to determine a new reward'),90).
rule(fix(self_regulatory_calming_same_reward, 'Function of Behavior : Calming category under Self Regulatory and Reward status : Sufficient.  Continue with same reward'),90).

rule(fix(self_regulatory_self_harm_new_reward,'Function_of_behavior : Self harm category under Self Regulatory and Reward status : Insufficient.  Consult a therapist to determine a new reward'),85).
rule(fix(self_regulatory_self_harm_same_reward,'Function_of_behavior : Self harm category under Self Regulatory and Reward status : Sufficient.  Continue with same reward'),85).



% askable descriptions

askable(socially_invalid).
askable(physically_harmful).
askable(physically_harm_themselves).
askable(physically_harm_others_or_things).
askable(receive_object).
askable(receive_activity).
askable(caused_trouble_after_some_event_occurance).
askable(destroyed_event_source).
askable(delayed_after_moved_away_from_event).
askable(stopped_after_moved_away_from_event).
askable(looks_at_other_people).
askable(calms_down_when_comforted).
askable(negative_trend_in_calming_time_with_current_reward).

