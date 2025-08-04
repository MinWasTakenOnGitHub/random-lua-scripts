local function ang2vec(angle_deg, eps)
    eps = eps or 0

    local signx = 1
    local signy = 1

    angle_deg = angle_deg % 360

    if angle_deg > 180 then
        angle_deg = angle_deg - 180
        signx = -1
        signy = -1
    end
    if angle_deg > 90 then
        angle_deg = 180 - angle_deg
        signx = -signx
    end 

    local xl, yl = 1, 0
    local xu, yu = 0, 1
    local cur   = 45
    local step  = 22.5

    while true do
        local sx, sy  = xl + xu, yl + yu
        local inv_len = 1 / math.sqrt(sx*sx + sy*sy)
        local xm, ym  = sx*inv_len, sy*inv_len

        if math.abs(cur - angle_deg) <= eps then
            return {x=signx * xm, y=signy * ym}
        end

        if cur > angle_deg then
            xu, yu = xm, ym
            cur    = cur - step
        else
            xl, yl = xm, ym
            cur    = cur + step
        end
        step = step * 0.5
    end
end

local function cos(deg)
    return ang2vec(deg).x
end

local function sin(deg)
    return ang2vec(deg).y
end
