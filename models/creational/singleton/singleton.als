module creatinal/singleton

sig Instance {}

sig Singleton {
    instance: lone Instance
}

fact singleton_instance {
    all disj s1, s2: Singleton | {
        #s1.instance = 1 
        #s2.instance = 1
    } => s1.instance = s2.instance
}

pred get_instance[s1, s2: Singleton] {
    #s1.instance = 0
    #s2.instance = 1
}

assert test_get_instance {
    all disj s1, s2, s3, s4: Singleton | {
        get_instance[s1, s2]
        get_instance[s3, s4]
    } => s2.instance = s4.instance
}

check test_get_instance for 6
