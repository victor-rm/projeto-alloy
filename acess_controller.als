sig user{
    org_user: lone organization,
    user_repositorys: set repository
}

sig organization{
    users: set user,
    org_repositorys: set repository
}

sig repository{
    collaborators: set user,
    org: one organization
}


fact {

    // eu ja não expecifico isso na assinatura ????
    // todo usuário pertence a pelo menos uma organização ou somente uma ??? duvida se é lone ou one 
	all u:user | lone u.org_user


    //Os usuários so podem acessar repositório da organização que pertence
	all u: user| some o: organization | u in o.users iff u.user_repositorys in o.org_repositorys

    //Os repositórios so podem ser de uma unica organização e a repositórios precisam apontar pra ela
    all r: repository | 
        one r.org
        and r in r.org.org_repositorys

    // um usuário pode ter no máximo 5 repositórios
    all u: user | # u.user_repositorys <= 5

    // aqui ja viajei, algum usuário tem algum repositorio 
    some u: user , r: repository| 
        u in r.collaborators and r in u.user_repositorys
}
// KKKKKKKKKKKKKkkk essa execução
run {} for 3
