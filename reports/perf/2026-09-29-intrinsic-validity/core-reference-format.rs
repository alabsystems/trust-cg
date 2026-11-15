use std::hint::black_box;
use std::net::{Ipv4Addr, Ipv6Addr, SocketAddrV4, SocketAddrV6};
fn main() {
    let v4 = [(0,0,0,0,"0.0.0.0"), (127,0,0,1,"127.0.0.1"), (192,168,20,250,"192.168.20.250"), (255,255,255,255,"255.255.255.255")];
    let v6 = [([0,0,0,0,0,0,0,0],"::"), ([0,0,0,0,0,0,0,1],"::1"), ([0x2001,0xdb8,0,0,0,0,0,1],"2001:db8::1"), ([1,2,3,4,5,6,7,8],"1:2:3:4:5:6:7:8")];
    let escaped = [("", ""), ("a\nb\t", "a\\nb\\t"), ("'\"\\", "\\'\\\"\\\\"), ("é🙂", "é🙂"), ("\0", "\\0")];
    let mut checks = 0;
    for _ in 0..1024 {
        for (a,b,c,d,want) in black_box(v4) {
            let ip = Ipv4Addr::new(a,b,c,d);
            assert_eq!(format!("{}", black_box(ip)), want);
            assert_eq!(format!("{}", black_box(SocketAddrV4::new(ip, 8080))), format!("{want}:8080"));
            checks += 2;
        }
        for (segments,want) in black_box(v6) {
            let ip = Ipv6Addr::from(segments);
            assert_eq!(format!("{}", black_box(ip)), want);
            assert_eq!(format!("{}", black_box(SocketAddrV6::new(ip, 1234, 0, 0))), format!("[{want}]:1234"));
            checks += 2;
        }
        for (input,want) in black_box(escaped) {
            assert_eq!(black_box(input).escape_debug().to_string(), want);
            checks += 1;
        }
    }
    println!("PASS linked_core_reference_format checks={checks}");
}
