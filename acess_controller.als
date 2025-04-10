/** 
-- Comentários de Massoni: inicio --

"Não é necessário ter ciclos assim, lembrando que relações em alloy não tem necessariamente direção"
Lobo: porém ta tudo ciclico aqui

"Vamos dizer que os usuários não necessariamente precisam estar em organizações...mas se estiverem, 
seguem as regras"
Lobo: não tem nada restringindo isso, então ta ok
 
"Quando falamos um sistema estamos falando da possibilidade de várias organizações independentes, certo?"
Lobo: o sistema permite organizações independentes

"Usuários podem estar sem usar nada"
Lobo: o sistema permite usuarios que não pertencem a organizações ou repos

Pergunta: "Os usuários podem acessa um repositório e não trabalhar nele?"
Massoni: "Nem todos os usuários precisam ser desenvolvedores" (significa que um Usuario pode não trabalhar em nenhum repo)

-- Comentários de Massoni: fim --

casos aceitáveis:
usuários sem repositórios (ok)
repositórios sem usuários (ok)

*/

sig Organization {
    repositories: set Repository,
    members: set User
}

sig Repository {
    owner: one Organization, // Cada repositório tem apenas uma organização
    collaborators: set User
}

sig User {
    belongsTo: lone Organization, // Cada usuário pertence a apenas uma organização
    interactsWith: set Repository,
    develop: set Repository
}

// Um usuário pode ter no máximo 5 repositórios 
pred userDevelopsConstraint[u: User] {
    #u.develop <= 5
    u.develop in u.interactsWith
    u.develop = { r: Repository | u in r.collaborators }
}

// Predicado para previnir de um repositorio pertencer a mais de uma organização
pred repoAndOrgReferenceIntegrity[o:Organization, r:Repository] {
    o = r.owner iff r in o.repositories
}

// Predicado para previnir o usuário de pertencer a mais de uma organização
pred userAndOrgReferenceIntegrity[u:User, o:Organization] {
    o = u.belongsTo iff u in o.members
}

pred userInteractsOnlyWithReposFromHisOrg[u: User] {
    all r: u.interactsWith | r.owner = u.belongsTo
}

pred userCanOnlyInteractIfMember[u: User] {
    all r: u.interactsWith | u in r.owner.members
}

pred userInteractsOnlyWithOwnOrgRepos[u: User] {
    userInteractsOnlyWithReposFromHisOrg[u] and userCanOnlyInteractIfMember[u]
}

pred exemplo {
    some o: Organization, u1, u2: User, r1, r2, r3: Repository |
        // Organização
        o.repositories = r1 + r2 + r3 and 
        
        r1.owner = o and 
        r2.owner = o and 
        r3.owner = o and 

        // Usuários pertencem à organização
        u1.belongsTo = o and 
        u2.belongsTo = o and 
        o.members = u1 + u2 and

        // u1 interage com 2 repositórios, desenvolve em 1
        u1.interactsWith = r1 + r2 and 
        u1.develop = r1 and 

        // u2 interage com os 3, desenvolve em 3 (válido porque <=5)
        u2.interactsWith = r1 + r2 + r3 and 
        u2.develop = r2 + r3 
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

assert DevOnlyDevelopsInOrgRepos {
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
check DevOnlyDevelopsInOrgRepos for 5
check UserOnlyInteractsWithOwnOrgRepos for 5
check UserOrgReferenceIntegrity for 5

run {} for 5 Organization, 3 User, 3 Repository

run exemplo for exactly 1 Organization, exactly 2 User, exactly 3 Repository
