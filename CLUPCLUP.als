abstract sig Bool { }
one sig True extends Bool {}
one sig False extends Bool {}

// MAC-address
one sig MAC {}

sig DateTime {
	year: one Int,
	month: one Int,
	day: one Int,
	hour: one Int,
	minute: one Int
} { 
// this values are just for modeling
	year >= 0 and
	month >= 0 and month =< 4 and
	day >= 1 and day =< 6 and
	hour >= 0 and
	minute >= 0
}

// in our case we suppose that UUID version 1defined as in RFC 4122
// so model it as the combination of MAC and datetime
// added by Sergey
sig UUID {
	dt: one DateTime,
	mac: one MAC
}

sig Location {
	lat: one Int,
	lon: one Int	
} {
// the values are for modeling
	lat >= -3 and lat =< 3 
	and lon >= -6 and lon =< 6
}

sig PhoneNo { }

sig Password { }

sig FullName { }

sig Address { }

sig Brand {}

sig RegCode {}

abstract sig Registration {
	phoneNo: one PhoneNo,
}

sig UserRegistration extends Registration {
}

sig StaffRegistration extends Registration{
	password: one Password,
}

sig MachineRegistration extends Registration {
	regCode: one RegCode
}

abstract sig User {
	fullName: one FullName,
}

sig PrivilegeUser extends User {
	reg: one StaffRegistration,
	store: some Store
}

abstract sig Customer extends  User {
	departments: set Department,
	queue: some Queue
}

sig CommonUser extends Customer {
	priority: one False,
	regC: one UserRegistration,
	location: some Location,
	b: some Booking
}

sig PrioritizedUser extends Customer {
	priority: one True,
	b: one Booking
}

sig Network {
	name: one Brand,
	addressHead: one Address,
	stores: some Store,
	staff: some PrivilegeUser
}

sig Store {
	address: one Address,
	capacity: one Int,
	deps: some Department,
	regM: some MachineRegistration
} {
	// the value for modeling
	capacity >= 1 and capacity =< 6
	
}

sig Department {
	koef: one Int,
	capacity: one Int,
	area: one Int
} {
	// the value for modeling
	koef >= 0 and koef =< 3 and
	capacity >= 1 and capacity =< 2 and
	area >= 0 and area =< 3
}

sig Queue {
	books: some Booking,
	store: one Store
}

sig Booking {
	position: one Int,
	// state indicates delete, create, enter, left
	state: one Int,
	selectedStore: one Store,
	bookingDate: DateTime,
	estimatedTime: DateTime,
	uuid: UUID,
	departureTime: DateTime,
} {
	position >= 0 and position =< 3 and
	state >= 0 and state =< 3
}

---------------------------<<facts>>------------------------------------------------

// fact. Networks HQ are not in the same address 
// we suppose we work with big shop networks like Auchan or 7-11
fact NoNetworkSameHQAddress {
	all disj n1, n2 : Network | n1.addressHead != n2.addressHead
}

// There is no two Networks have the same store
// but two or more stores in different networks may have the same address
fact NoNetworkHasTheSameStore {
	all disj n1, n2: Network |  n1.stores != n2.stores
}

// fact. Every store must have a network
fact EveryStoreMustHaveANetwork {
	all s : Store | one  n: Network | s in n.stores
}

// fact. We think it's not good to have the same Network stores share the same address
fact NoStoreNetworkShareTheSameAddress {
	all disj s, s': Store | one n: Network |  s in n.stores and s' in n.stores implies s.address != s'.address
}

// fact. PhoneNo are unique if user are not staff
fact PhoneNoUnique {
	all  disj r, r': Registration | r.phoneNo != r'.phoneNo
}

// fact Passwords are unique
fact PassUnique {
	all  disj r, r': StaffRegistration | r.password != r'.password
}

// fact two staff can't have the same registration
fact RegistrationStaffUnique {
	all disj st, st': PrivilegeUser | st.reg != st'.reg
}

// fact CommonUser can't have the same registration
fact CommonUserUnique {
	all disj c, c': CommonUser | c.regC != c'.regC
}

// fact MachineReg is unique
fact MachineUnique {
	all disj s, s': Store | s.regM not in s'.regM
}

// fact users can't have the same username
fact UsernameUnique {
	all u, u' : User | u != u' implies u.fullName != u'.fullName
}

// fact PrivilegeUser must work in the Network
fact NetworkStaff {
	all n : Network | all p:PrivilegeUser | p in n.staff
}

// fact every store must have departments (delete the hanging departmens)
fact DepartmentStore {
	all d : Department | one s: Store | d in s.deps
}

// fact queue can't hanging
//fact QueueToController {
//	all q: Queue | one s: SessionController | q in s.queue 
//}

// fact booking can't hanging
fact BookToQueue {
	all b: Booking | one q: Queue | b in q.books
}

// fact Queues are unique
fact UniqueQueue {
	all disj q, q': Queue | q != q' implies q.store != q'.store
}

// uuid are unique
fact UUIDUnique {
	all disj b1, b2 : Booking | b1 != b2 implies b1.uuid != b2.uuid
}

// fact Store the same for Queue and for Booking
fact UniqueStoreQueue {
	all b: Booking | some q: Queue | b in q.books implies b.selectedStore =  q.store
}

//fact regCode unique
fact RegCodeUnique {
	all disj m1, m2: MachineRegistration | m1.regCode != m2.regCode
}

-------------<predicates>-------------------------------------------------------- 


pred w1 {
	#Department = 5
	#CommonUser = 2
	#PrioritizedUser = 1
	#Booking = 2
	#Store = 2
	#Queue = 1
	(some disj b1, b2: Booking | b1.bookingDate != b2.bookingDate)
}

run w1 for 5 but  2 MachineRegistration, 1 PrioritizedUser, 1 PrivilegeUser

pred w2 {
	#PrivilegeUser = 5
	#Store = 2
}

run w2 for 7 

pred w3 {
	#Department = 2
	#CommonUser = 2
	#Booking = 2
	#Store = 2
	#Queue = 2
	(some disj b1, b2: Booking | b1.selectedStore != b2.selectedStore 
			implies b1.bookingDate = b2.bookingDate)
}

run w3 for 5 but  2 MachineRegistration, 1 PrioritizedUser, 1 PrivilegeUser
