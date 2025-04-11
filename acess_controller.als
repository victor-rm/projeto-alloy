// Grupo: 
// Victor Jacob Oliveira Rodrigues da Silva - 122210374
// Pedro Lôbo Nascimento - 122210558
// Tarcisio Araújo de Oliveira - 123210061
// Luiza Oliveira de Carvalho - 123210054
// Victor Ribeiro Miranda - 123210384 

sig Organization {
    repositories: set Repository,  // Cada organização tem um conjunto de Repositórios
    members: set User  // Cada organização tem um conjunto de Usuários
}

sig Repository {
    owner: one Organization,  // Cada repositório tem apenas uma Organização
    collaborators: set User  // Cada repositório tem um conjunto de Usuários
}

sig User {
    belongsTo: lone Organization,  // Cada usuário pertence a apenas uma organização
    interactsWith: set Repository,  // Cada usuário interage com um conjunto de Repositórios
    develop: set Repository  // Cada usuário desenvolve em um conjunto de Repositórios
}

// Um usuário pode ser desenvolvedor em, no máximo, 5 repositórios 
pred userDevelopsConstraint[u: User] {
    #u.develop <= 5
    u.develop in u.interactsWith
    u.develop = { r: Repository | u in r.collaborators }
}

// Predicado para previnir que um repositorio pertença a mais de uma organização
pred repoAndOrgReferenceIntegrity[o:Organization, r:Repository] {
    o = r.owner iff r in o.repositories
}

// Predicado para previnir o usuário de pertencer a mais de uma organização
pred userAndOrgReferenceIntegrity[u:User, o:Organization] {
    o = u.belongsTo iff u in o.members
}

// Predicado para que um usuário interaja apenas com repositórios de sua mesma organização
pred userInteractsOnlyWithReposFromHisOrg[u: User] {
    all r: u.interactsWith | r.owner = u.belongsTo
}

// O usuário só pode interagir com um repositório se for membro de sua mesma organização
pred userCanOnlyInteractIfMember[u: User] {
    all r: u.interactsWith | u in r.owner.members
}

// O usuário só pode interagir com repositórios que fazem parte da organização da qual ele é membro
pred userInteractsOnlyWithOwnOrgRepos[u: User] {
    userInteractsOnlyWithReposFromHisOrg[u] and userCanOnlyInteractIfMember[u]
}

pred exemplo {
    some o1: Organization, u1, u2: User, r1, r2, r3: Repository |
        --> Organização 1
        o1.repositories = r1 + r2 + r3 and 
        
        r1.owner = o1 and
        r2.owner = o1 and 
        r3.owner = o1 and 

        --> Usuários pertencem à organização
        u1.belongsTo = o1 and 
        u2.belongsTo = o1 and 
        o1.members = u1 + u2 and

        --> u1 interage com 2 repositórios, desenvolve em 1
        u1.interactsWith = r1 + r2 and 
        u1.develop = r1 and
        r1.collaborators = u1 and 

        --> u2 interage com os 3, desenvolve em 3
        u2.interactsWith = r1 + r2 + r3 and 
        u2.develop = r2 + r3 and
        r2.collaborators = u2 and
        r3.collaborators = u2
}

fact {

    all r:Repository, o:Organization | 
        repoAndOrgReferenceIntegrity[o,r]

    all u:User, o:Organization |
         userAndOrgReferenceIntegrity[u,o]

    all u: User |
        userDevelopsConstraint[u]

    all u: User | 
        userInteractsOnlyWithOwnOrgRepos[u]
}

assert UserDevelopsWithinInteractionLimit {
    all u: User | #u.develop <= 5 and u.develop in u.interactsWith
}

assert AllDevelopersAreCollaborators {
    all u: User, r: Repository |
     r in u.develop implies u in r.collaborators
}

assert AllCollaboratorsAreOrgsMembers {
    all u: User, r: Repository |
     u in r.collaborators implies u in r.owner.members
}

assert UserOnlyDevelopsInOrgRepos {
    all u: User | all r: u.develop | r.owner = u.belongsTo
}

assert UserOnlyInteractsWithOwnOrgRepos {
    all u: User, r: u.interactsWith | r.owner = u.belongsTo
}

assert UserOrgReferenceIntegrity {
    all u: User, o: Organization | o = u.belongsTo iff u in o.members
}

check UserDevelopsWithinInteractionLimit for 5

check AllDevelopersAreCollaborators  for 5

check AllCollaboratorsAreOrgsMembers for 5

check UserOnlyDevelopsInOrgRepos for 5

check UserOnlyInteractsWithOwnOrgRepos for 5

check UserOrgReferenceIntegrity for 5

run {} for 5 

run exemplo for 5


// Mais alguns runs para cenários específicos

run exemplo for exactly 1 Organization, exactly 2 User, exactly 3 Repository

run {} for exactly 3 Organization, exactly 4 User, exactly 6 Repository