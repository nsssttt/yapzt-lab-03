module computer_network_v5

abstract sig ChannelDirection {}
one sig OneWay, TwoWay extends ChannelDirection {}

sig Computer {}

sig Channel {
    source: one Computer,
    target: one Computer,
    direction: one ChannelDirection
}

one sig Network {
    computers: some Computer,
    channels: set Channel
}

fun links[n: Network]: Computer -> Computer {
    {a, b: n.computers |
        some ch: n.channels |
            (ch.source = a and ch.target = b)
            or (ch.direction = TwoWay and ch.source = b and ch.target = a)
    }
}

fact AtLeastTwoComputers {
    #Network.computers >= 2
}

fact ChannelEndpointsAreInNetwork {
    all c: Network.channels |
        c.source in Network.computers
        and c.target in Network.computers
        and c.source != c.target
}

fact AllComputersBelongToOnePhysicalNetwork {
    all disj a, b: Network.computers |
        b in a.^(links[Network] + ~(links[Network]))
}

pred hasIsolatedComputer {
    some c: Network.computers |
        no c.(links[Network]) and no c.~(links[Network])
}

pred hasDirectedCycle {
    some c: Network.computers |
        c in c.^(links[Network])
}

pred acyclicNetwork {
    no c: Network.computers |
        c in c.^(links[Network])
}

assert NoIsolatedComputer {
    no c: Network.computers |
        no c.(links[Network]) and no c.~(links[Network])
}

run hasIsolatedComputer for 4
run hasDirectedCycle for 4
run acyclicNetwork for 4
check NoIsolatedComputer for 4
