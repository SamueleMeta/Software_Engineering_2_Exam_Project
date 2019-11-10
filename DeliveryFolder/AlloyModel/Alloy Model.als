-- We import util/boolean to have a boolean variable that indicates if a User is verified or not
open util/boolean

--------------------SIGNATURES----------------------
---------- Users
abstract sig User{}
sig Username, AuthorityID, FiscalCode, Email, Plate{}

-- A Logged User represents both Citizens and Authorities common features:
-- each of them has an unique username and an unique email
abstract sig LoggedUser extends User{
	username: one Username,
	email: one Email,
	verified: one Bool
}

-- A Citizen indicates an unique FiscalCode to register, the date
-- of birth in order to let the application making constraints by age.
-- Further we have the set of ViolationRepors sent to the app and 
-- a set of AreasStatistics showed
sig Citizen extends LoggedUser{
	fiscalcode: one FiscalCode,
	dateOfBirth: one Date,
	violations: set ViolationReport,
	areasStat: set AreasStatistic
}{dateOfBirth.year < 4} // We simulate a constraint on the age of the Citizen

sig Date{
	year: one Int // For semplicity we use alloy's Int data type
}{year > 0}

-- An Authority instead uses an AuthorityID to register. Here we have
-- also a set of accepted ViolationReports and all the sets of consulted Statistics
-- (an Authority can view statistics about Areas, Vehicles or Interventions)
sig Authority extends LoggedUser{
	authorityID : one AuthorityID,
	violations: set ViolationReport,
	areasStat: set AreasStatistic,
	vehiclesStat: set VehiclesStatistic,
	interventionsStat: set InterventionsStatistic
}



---------- Violations
sig Picture, StreetName{}

-- A ViolationReport has an unique id, a set of Pictures taken by the Citizen (saved
-- as "user"), the plate of the vehicles (in order to send it to the ViolationManager)
-- and the position of the violation
sig ViolationReport{
	id: one Int,
	pictures: set Picture,
	user: one Citizen,
	position: one Position,
	plate: one Plate
}{#pictures > 0 and #pictures <= 4 and id > 0} // We want a positive id and we set constraints on the number of photos
																			   // (to prevent infinite loops or security attacks)

-- A Position is made of longitude and latitude (Int for semplicity).
-- Furthermore we add the StreetName retrived by the system
sig Position{
	longitude: one Int,
	latitude: one Int,
	streetName: one StreetName
}

-- The real ViolationManager has lots of functionalities; here we focus on the fact
-- that we need a manager that retrieves information from the violations and sends
-- them to a MiningManager to permit statistics creation
one sig ViolationManager{
	violations: set ViolationReport,
	miningManager: one MiningManager // The MiningManager is unique in the model
}



---------- Statistics
one sig MiningManager{
	areasStat: set AreasStatistic,
	vehiclesStat: set VehiclesStatistic,
	interventionsStat: set InterventionsStatistic
}

-- Each Statistic has an id in order to be uniquely identified
abstract sig Statistic{
	id: one Int
}{id > 0}

-- Follow different types of Statistics
sig AreasStatistic extends Statistic{}

sig VehiclesStatistic extends Statistic{}

sig InterventionsStatistic extends Statistic{}



--------------------FACTS--------------------
-- I must ensure that some elements don't exist without the existance of other ones
fact existentiality{
	-- There is not a username not linked to a LoggedUser
	no u: Username | no l: LoggedUser | l.username = u
	-- Same thing for email, date
	no e: Email | no l: LoggedUser | l.email = e
	no d: Date | no c:Citizen | c.dateOfBirth= d
	-- There is not a FiscalCode or an AuthorityID without the respectively Users
	no f: FiscalCode | no c:Citizen | c.fiscalcode= f
	no au: AuthorityID | no a:Authority | a.authorityID = au
	-- There is not any ViolationReport not linked to a Citizen who made it
	no v: ViolationReport | no c: Citizen | v in c.violations
	-- There is not Positions and Pictures without a linked ViolationReport
	no p:Position | no v:ViolationReport | v.position = p
	no p: Picture | no v: ViolationReport | p in v.pictures
	-- There is not any StreetName without a Position
	no s:StreetName | no p:Position | p.streetName = s

	-- There is not any type of Statistic if not present in the Mining Manager
	no a: AreasStatistic | no m:MiningManager | a in m.areasStat
	no v: VehiclesStatistic | no m:MiningManager | v in m.vehiclesStat
	no i: InterventionsStatistic | no m:MiningManager | i in m.interventionsStat
}

-- I must ensure that some of the attributes of some of the Signatures are unique
fact unicity{
	-- There are not 2 different Citizens with the same FiscalCode
	no disj c1, c2: Citizen | c1.fiscalcode = c2.fiscalcode
	-- There are not 2 different ViolationReports with the same id
	no disj v1, v2: ViolationReport | v1.id = v2.id
	-- There are not 2 different LoggedUsers with the same Username
	no disj l1, l2: LoggedUser | l1.username = l2.username
	-- There are not 2 different LoggedUser with the same Email
	no disj l1, l2: LoggedUser | l1.email = l2.email
	-- There are not 2 different ViolationReports that contain the same photo
	no disj v1,v2: ViolationReport | v1.pictures & v2.pictures != none
	-- There are not 2 different Citizens that have the same ViolationReport in their history
	no disj c1,c2: Citizen | c1.violations & c2.violations != none
	-- There are not 2 different Authorities that have the same accepted ViolationReport
	-- (a Violation Report is accepted by only an Authority)
	no disj a1,a2: Authority | a1.violations & a2.violations != none
	-- There are not 2 different Statistics (whatever the type of statistic is)
	-- that are identified by the same id
	all a: AreasStatistic, v: VehiclesStatistic, i: InterventionsStatistic | a.id != v.id and a.id != i.id and v.id != i.id
}

-- I must ensure that all the LoggedUser are verified or not
fact verifiedOrNot{
	all l:LoggedUser | l.verified = False or l.verified = True
}

-- I must ensure that if the Citizen is not verified no violations are in the set,
-- in the same way also if an Authority is not verified no violations can be accepted
fact name{
	all a: Authority | a.verified = False iff #(a.violations) = 0
	all c: Citizen | c.verified = False iff #(c.violations) = 0
}

-- I must ensure that the "user" field of a ViolationReport is the same unique Citizen who 
-- have that in the set of violations
fact uniqueCitizenLink{
	all v:ViolationReport, c:Citizen | v.user = c iff v in c.violations
}

-- I must ensure that all the AreasStatics consulted by some Authorities or Citizens are the ones the MiningManager has created;
-- instead for VehiclesStatistics and InterventionsStatistics we ensure the same thing only for Authorities
fact StatisticsConstraints{
	all m: MiningManager, ar: AreasStatistic | some a: Authority | ar in a.areasStat implies ar in m.areasStat
	all m: MiningManager, ar: AreasStatistic | some c: Citizen | ar in c.areasStat implies ar in m.areasStat
	all m: MiningManager, ve: VehiclesStatistic | some a: Authority | ve in a.vehiclesStat iff ve in m.vehiclesStat
	all m: MiningManager, i: InterventionsStatistic | some a: Authority | i in a.interventionsStat iff i in m.interventionsStat
}

-- I must ensure that the ViolationManager contains all the ViolationReports
fact allReportsInViolationManager{
	all v: ViolationReport, vm: ViolationManager | v in vm.violations
}



--------------------ASSERTIONS AND PREDICATES--------------------
-- We assert that any ViolationReport is sent by an unique Citizen
assert noReportsWithoutCitizen{
	all v:ViolationReport | one c:Citizen | v in c.violations
}

pred show{
# Statistic > 2
}

pred addViolationReport[c: Citizen, v: ViolationReport]{
	c.violations = c.violations + v
	v.user = c
}

pred showAreasStatistic[c: Citizen, ar: AreasStatistic]{
	c.areasStat = c.areasStat + ar
}

pred acceptViolationReport[a: Authority, v: ViolationReport]{
	a.violations = a.violations + v
}


--------------------CHECKS AND RUNS--------------------
check noReportsWithoutCitizen

run show for 7 but exactly 1 Citizen, 2 Authority, 3 Picture, 2 ViolationReport

run show for 7 but exactly 3 Citizen, 1 Authority, 5 ViolationReport

run addViolationReport for 7 but exactly 1 Citizen

run showAreasStatistic for 7 but exactly 2 Authority

run acceptViolationReport for 7 but exactly 3 ViolationReport
