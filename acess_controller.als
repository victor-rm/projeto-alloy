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
    belongsTo: one Organization // Cada repositório tem apenas uma organização
}

sig User {
    belongsTo: lone Organization, // Cada usuário pertence a apenas uma organização
    interactsWith: set Repository
}

// Um usuário pode ter no máximo 5 repositórios 
pred userInteractsWithAtMost5Repos[u:User] {
    #u.interactsWith >= 0 and #u.interactsWith <= 5
}

// Um usuário pode interagir apenas com repositórios da organização que ele pertence
pred userInteractsOnlyWithOwnOrgRepos[u:User, o:Organization, r:Repository] {
    r in u.interactsWith iff (r in o.repositories and u in o.members)
}

// Predicado para previnir de um repositorio pertencer a mais de uma organização
pred repoAndOrgReferenceIntegrity[o:Organization, r:Repository] {
    o = r.belongsTo iff r in o.repositories
}

// Predicado para previnir o usuário de pertencer a mais de uma organização
pred userAndOrgReferenceIntegrity[u:User, o:Organization] {
    o = u.belongsTo iff u in o.members
}

pred userInteractsOnlyWithReposFromHisOrg[u: User] {
    all r: u.interactsWith | r.belongsTo = u.belongsTo
}

pred userCanOnlyInteractIfMember[u: User] {
    all r: u.interactsWith | u in r.belongsTo.members
}

pred userInteractsOnlyWithOwnOrgRepos[u: User] {
    userInteractsOnlyWithReposFromHisOrg[u] and userCanOnlyInteractIfMember[u]
}

fact {

    all r:Repository, o:Organization | 
        repoAndOrgReferenceIntegrity[o,r]

    all u:User, o:Organization |
         userAndOrgReferenceIntegrity[u,o]

    all u:User |
         userInteractsWithAtMost5Repos[u]

    all u: User | 
        userInteractsOnlyWithOwnOrgRepos[u]
}
// Faltam fazer os asserts

assert UserHasAtMost5Repos {
    all u: User | #u.interactsWith >= 0 and #u.interactsWith <= 5
}
check UserHasAtMost5Repos

assert UserOnlyInteractsWithOwnOrgRepos {
    all u: User, r: u.interactsWith | r.belongsTo = u.belongsTo
}
check UserOnlyInteractsWithOwnOrgRepos


assert UserOrgReferenceIntegrity {
    all u: User, o: Organization | o = u.belongsTo iff u in o.members
}
check UserOrgReferenceIntegrity

run {} for exactly 4 Organization, exactly 5 User, exactly 5 Repository
