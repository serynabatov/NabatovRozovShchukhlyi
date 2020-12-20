abstract sig Bool {}
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
// these values are just for modeling
    year >= 0 and
    month >= 0 and month =< 4 and
    day >= 1 and day =< 6 and
    hour >= 0 and
    minute >= 0
}

// in our case we suppose that UUID version 1defined as in RFC 4122
// so model it as the combination of MAC and datetime
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

sig PhoneNo {}

sig Password {}

sig FullName {}

sig Address {}

sig Brand {}

sig Registration {
    phoneNo: one PhoneNo,
}

sig StaffRegistration extends Registration {
    password: one Password,
}

abstract sig User {
    fullName: one FullName,
}

sig PrivilegeUser extends User {
    reg: one StaffRegistration,
    store: some Store
}

abstract sig Customer extends User {
    departments: set Department,
    regC: one Registration,
    control: set SessionController
}

sig MachineReq {} //

sig CommonUser extends Customer {
    priority: one False
}

sig PrioritizedUser extends Customer {
    priority: one True
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
    deps: some Department
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

sig SessionController {
    queue: some Queue,
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
    // estimatedTime in booking must be equal to difference between departureTime
    // and bookingDate
    // departureTime = bookingDate + estimatedTime
    position >= 0 and position =< 3 and
    state >= 0 and state =< 3
}

// fact. Networks HQ are not in the same address
// we suppose we work with big shop networks like Auchan or 7-11
fact NoNetworkSameHQAddress {
    all disj n1, n2 : Network | n1 != n2 implies n1.addressHead != n2.addressHead
}

// There is no two Networks have the same store
// but two or more stores in different networks may have the same address
fact NoNetworkHasTheSameStore {
    all disj n1, n2: Network | n1 != n2 implies n1.stores != n2.stores
}

// fact. Every store must have a network
fact EveryStoreMustHaveANetwork {
    all s : Store | one n: Network | s in n.stores
}

// fact. We think it's not good to have the same Network stores share the same address
fact NoStoreNetworkShareTheSameAddress {
    all disj s, s': Store | one n: Network |  s in n.stores and s' in n.stores implies s.address != s'.address
}

// fact. PhoneNo are unique if user are not staff
fact PhoneNoUnique {
    all r, r': Registration | r != r' implies r.phoneNo != r'.phoneNo
}

// fact Passwords are unique
fact PassUnique {
    all r, r': StaffRegistration | r != r' implies r.password != r'.password
}

// fact two users can't have the same registration
// There are some users in fact that are staff and customers at the same time
// Because as we saw earlier the functionality differs
fact RegistrationUnique {
    // exclude the prioritizeduser; think about this one. It's not so obvious as you thought
    all u, u': User | u != u'  implies u.reg != u'.reg or u.regC != u'.regC
}

// fact users can't have the same username
fact UsernameUnique {
    all u, u' : User | u != u' implies u.fullName != u'.fullName
}

// fact PrivilegeUser must work in the Network
fact NetworkStaff {
    all n : Network | all p:PrivilegeUser | p in n.staff
}

// fact story capacity must be more than departments
//fact StoreIsBiggerThanDepartments {
//  all s : Store | all d : Department | d in s.deps implies sum s.d.capacity <= s.capacity
//}

// fact every store must have departments (delete the hanging departmens)
fact DepartmentStore {
    all d : Department | one s: Store | d in s.deps
}

// fact the controller is only one. It emulates the real controller
// a person that regulates the flow
fact ControllerTheOne {
    all c: Customer | one s:  SessionController| s in c.control
}

// fact queue can't hang
fact QueueToController {
    all q: Queue | one s: SessionController | q in s.queue
}

// fact booking can't hang
fact BookToQueue {
    all b: Booking | one q: Queue | b.selectedStore = q.store  implies b in q.books
}

// fact Queues are unique
fact UniqueQueue {
    all disj q, q': Queue | q != q' implies q.store != q'.store
}

// uuid are unique
fact UUIDUnique {
    all disj b1, b2 : Booking | b1 != b2 implies b1.uuid != b2.uuid
}

pred show() {
    #PrivilegeUser = 2
    #Department = 5
    #CommonUser = 2
    #SessionController = 1
    #PrioritizedUser = 1
    //#Booking = 1
    #Store = 3
    #Queue = 2
}

run show for 10
