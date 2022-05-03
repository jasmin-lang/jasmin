using Base.Filesystem
using Printf

function wc(filename)
    if Filesystem.isfile(filename)
        open(countlines, filename, "r")
    else
        0
    end
end

models = [ "CL32" "CL64" "BL" "TV_CL32" "TV_CL64" "TV" ]
rotate_offset = [ "BL" "TV" ]
rotate_mac = [ "BL" "CL32" "CL64" ]

file(ro, rm, m) = "copy_mac_ct_proof_$(ro)_$(rm)_$(m).ec"

for m in models
    Printf.@printf "\t%s" m
end
Printf.@printf "\n"

for rm in rotate_mac
    for ro in rotate_offset
        Printf.@printf "%s_%s" ro rm
        for m in models
            Printf.@printf "\t%d" wc(file(ro, rm, m))
        end
        Printf.@printf "\n"
    end
end
Printf.@printf "\n"
