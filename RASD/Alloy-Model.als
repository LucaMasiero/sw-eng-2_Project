enum TournamentState {OpenRegistration, OnGoing, Closed}
enum BattleState {Registration, Active, Consolidation, Ended}

abstract sig User{}

sig Student extends User{}

/*All Educators could be owners of a tournament and colleague with permissions in another tournament*/
sig Educator extends User{}

sig Tournament{
	var state: one TournamentState,
	creator: one Educator,
	var assistants: set (Educator - creator), /*The colleagues with permissions to create a battle*/
	var battles: set Battle,
	var registered: set Student
}

sig Battle{
	var state: one BattleState,
	var teams: set Team,
	creator: one Educator
}

sig Team{
	var components: disj some Student,
	score: disj one Score 
}

sig Score {
	var value: disj one Int
}{
	value >= 0 and value <= 100
}

/************** FUNCTIONS ***********/

/* This function returns the state of a tournament */
fun tournamentState [t: Tournament] : one TournamentState {
	t.state
}

/* This function returns the state of a battle */
fun battleState [b: Battle]: one BattleState {
	b.state
}

/************** FACTS  ****************/
/* An educator can't be both a creator and an assistant for a Tournament, and reinforces 
    what the 'assistants' field in the Tournament signature already states 
*/
fact NoCreatorIsAssistant {
 	all t: Tournament | t.creator not in t.assistants
}

/* A tournament has no battle during the registration period*/
fact tournamentHasNoBattleInRegistrationPeriod {
	all t: Tournament | tournamentState[t] = OpenRegistration
	implies
	no t.battles
}

/*A Closed tournament can only contain Ended battles*/
fact closedTournamentMeansEndedBattles{
	all t: Tournament | tournamentState[t] = Closed
	implies
		all b: Battle | b in t.battles
		implies
		battleState[b] = Ended
}

/* The creator of a battle is either the creator of the tournament 
    containing the battle or an educator who has been granted the permissions to create one*/
fact creatorOfBattle{
	all b: Battle, t:Tournament | b in t.battles
	implies
	(b.creator in (t.creator + t.assistants)) 
}

/*The students in the teams participating to a battle must also be registered to the Tournament 
containing that battle*/
fact correctRegistration{
	all b: Battle, t: Team, s: Student | s in t.components and t in b.teams
	implies
	one t: Tournament | b in t.battles and s in t.registered
}

/*A team exist only in the context of a battle:
   there can't be a team that does not participate to any battle*/
fact noTeamsOutsideBattles{
	all t: Team | one b: Battle | t in b.teams
}

/*A battle exists only in the context of a tournament:
    there can't be a battle which is not contained into a tournament*/
fact noBattleOutsideTournaments{
	all b: Battle | one t: Tournament | b in t.battles
}

/*A score exists only in the context of a Team:
   there can't be a score that is not relted to any team*/
fact noScoreWithoutTeam{
	all sc: Score | one t: Team | sc in t.score
}

/*If an educator is creator of a tournament he will always be*/
fact{
	all t: Tournament, c: Educator| c = t.creator
	implies
	after always t.creator = c
}

/*If an educator is assistant of a tournament he will always be*/
fact{
	all t: Tournament, a: Educator| a in t.assistants
	implies
	after always a in t.assistants
}

/*If a battle belongs to a turnament it will always do*/
fact{
	all b: Battle, t: Tournament | b in t.battles
	implies
	after always b in t.battles
}

/*If a student is part of a team he will always be*/
fact{
	all s: Student, t: Team | s in t.components
	implies
	after always s in t.components
}

/*If a student is registered for a tournament, he will always be*/
fact{
	all s: Student, t: Tournament | s in t.registered
	implies
	after always s in t.registered
}

/*If a team is registered for a battle, it will always be */
fact{
	all t: Team, b: Battle | t in b.teams
	implies
	after always t in b.teams
}

//Life cycle of a tournament
/* OpenRegistration → OnGoing ...*/
fact{
	all t: Tournament | 
		always ( tournamentState[t] = OpenRegistration
			implies
			historically tournamentState[t] = OpenRegistration and
			eventually tournamentState[t] = OnGoing)
}
// ...OnGoing → Closed
fact{
	all t: Tournament | 
		always (tournamentState[t] = Closed
			implies
			once tournamentState[t] = OnGoing and
			after always tournamentState[t] = Closed)
}

// Life cycle of a battle..
// Registration → Active
fact{
	all b: Battle | 
		always (battleState[b] = Registration
			implies
			historically battleState[b] = Registration and
			eventually battleState[b] = Active)
}
// Active → Consolidation
fact{
	all b: Battle | 
		always (battleState[b] = Active
			implies
			eventually battleState[b] = Consolidation) 
}
//Consolidation → Ended
fact{
	all b: Battle | 
		always (battleState[b] = Consolidation
			implies
			eventually battleState[b] = Ended) 
}
// Ended
fact{
	all b: Battle | 
		always (battleState[b] = Ended
			implies
			once battleState[b] = Consolidation and
			after always battleState[b] = Ended) 
}


/********* PREDICATES ***************/

/* Assistant added to a tournament */
pred addAssistantToTournament [t:Tournament, e: Educator]{
	e not in t.assistants
	after (e in t.assistants and tournamentState[t] != Closed)
}

/* Student registers to a tournament whose state is OpenRegistration */
pred registerStudentToTournament[t: Tournament, s: Student] {
	s not in t.registered
	after (s in t.registered and tournamentState[t] = OpenRegistration)
}

pred studentJoinTeam[t: Team, s: Student, b: Battle]{
	s not in t.components and t in b.teams
	after (s in t.components)
}

pred addBattleToTournament[t: Tournament, b: Battle] {
	tournamentState[t] = OnGoing and b not in t.battles
	after ( tournamentState[t] = OnGoing and b in t.battles)
}

pred world {
	#Team = 3
	#Student > 3
	#Tournament = 2
	#Battle > 2
}

/************** ASSERTIONS ****************/

/*This assert checks that there is no battle that has as its creator an educator who is not the creator 
   of the tournament or does not have permissions for the tournament to which that battle belongs*/
assert noCreationWithoutPermissions {
	all b: Battle, t: Tournament | b in t.battles
	implies
	b.creator in ( t.creator + t.assistants)
}

/*This assert checks that there aren't students registered to a battle without being registered 
    for the tournament containing the battle*/
assert noWrongRegistrations {
	all b: Battle, t: Team, s: Student | s in t.components and t in b.teams
	implies
	one t: Tournament | b in t.battles and s in t.registered
}

//run world for 7 but 8 Int

//run addAssistantToTournament for 3 but 1 Tournament

//run registerStudentToTournament for 3 but 1 Tournament

//run studentJoinTeam for 8 Int

run addBattleToTournament for 3 but 2 Tournament, 8 Int


//check  noCreationWithoutPermissions 

//check noWrongRegistrations 

