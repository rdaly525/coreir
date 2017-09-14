DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
if [ "$#" -eq 2 ];
then
    nuXmv -pre cpp -bmc -bmc_length $1 -source $DIR/nuXmv_commands.txt $2
else
    nuXmv -pre cpp -source $DIR/nuXmv_commands.txt $1
fi
